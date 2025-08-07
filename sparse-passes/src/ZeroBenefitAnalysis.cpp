#include <stdlib.h>
#include <algorithm>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/Constants.h>
#include <string>
#include <utility>
#include <utils.h>
#include <FunctionJIT.h>
#include "ZeroBenefitAnalysis.h"
#include "boost/graph/adjacency_matrix.hpp"
#include "boost/graph/reverse_graph.hpp"
#include "boost/graph/transitive_closure.hpp"
#include "GraphBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/ExecutionEngine/Orc/ThreadSafeModule.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Casting.h"
#include "llvm/ExecutionEngine/Orc/Core.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Error.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include <boost/graph/adjacency_list.hpp>
#include <cstring>
#include <functional>
#include <llvm/IR/Function.h>
#include <llvm/Transforms/Utils/LCSSA.h>
#include <llvm/Transforms/Utils/LoopSimplify.h>
#include <llvm/Transforms/Utils/ValueMapper.h>
#include <memory>
#include <vector>
#include <queue>
#include <unordered_set>
#include <unordered_map>
#include "developing.h"
#include "probe.h"
#include "probe_helper.h"
#include "dominance.h"
#include "userop.h"
#include <chrono>
using std::unordered_map;
using std::unordered_set;
using std::vector;
using namespace llvm;

// #define dbgs dummy_dbgs

using std::priority_queue;

bool isEffectiveCall(Value *v)
{
    if (auto call = dyn_cast<CallInst>(v))
    {
        if (call->getFunction()->getName() == "llvm.exp.f64")
        {
            return false;
        }
        auto effects = call->getFunction()->getMemoryEffects();
        return !effects.doesNotAccessMemory() && !effects.onlyReadsMemory();
    }
    else if (auto invoke = dyn_cast<InvokeInst>(v))
    {
        auto effects = invoke->getFunction()->getMemoryEffects();
        return !effects.doesNotAccessMemory() && !effects.onlyReadsMemory();
    }
    return false;
}
// template <typename T>
// class span2d
// {
// private:
//     T *data;
//     size_t rows;
//     size_t cols;

// public:
//     span2d(T *data, size_t rows, size_t cols)
//     : data(data)
//     , rows(rows)
//     , cols(cols)
//     {
//     }
//     T &operator()(size_t row, size_t col) { return data[row * cols + col]; }
//     const T &operator()(size_t row, size_t col) const { return data[row * cols + col]; }
// };

using PropagationFuncInfo = unordered_map<std::string, vector<int>>;
PropagationFuncInfo loadPropagationFuncInfo()
{
    unordered_map<std::string, vector<int>> propagation_func_info;
    if (auto path = getenv("PROPAGATION_FUNC_PATH"))
    {
        my_dbg() << "load propagation func from " << path << "\n";
        FILE *f = fopen(path, "r");
        char buffer[1024];
        while (true)
        {
            fgets(buffer, 1024, f);
            if (feof(f))
            {
                break;
            }
            llvm::StringRef line(buffer);
            SmallVector<llvm::StringRef, 4> tokens;
            line.split(tokens, " ");
            // my_dbg() << "line: " << line << "\n";
            // my_dbg() << "tokens: " << tokens[0] << "\n";
            for (int i = 1; i < tokens.size(); ++i)
            {
                propagation_func_info[tokens[0].str()].push_back(std::stoi(tokens[i].str()));
            }
        }
    }
    return propagation_func_info;
}

bool isFullZeroSensitive(llvm::Instruction *inst)
{
    if (isa<CastInst>(inst))
    {
        return true;
    }

    unsigned zero_sensitive_opcodes[] = {
        Instruction::Mul,
        Instruction::And,
        Instruction::FMul,
        Instruction::FNeg,
        Instruction::FPExt,
        Instruction::FPTrunc,
        Instruction::SExt,
        Instruction::ZExt,
        Instruction::Trunc,
        Instruction::UIToFP,
        Instruction::SIToFP,
        Instruction::FPToUI,
        Instruction::FPToSI,

    };
    for (auto opcode : zero_sensitive_opcodes)
    {
        if (inst->getOpcode() == opcode)
        {
            return true;
        }
    }
    return false;
}

bool isPartialZeroSensitive(llvm::Instruction *inst, int operand_index)
{
    if (operand_index == 0)
    {
        unsigned first_op_zero_sensitive_opcodes[] = {
            Instruction::UDiv,
            Instruction::SDiv,
            Instruction::FDiv,
            Instruction::URem,
            Instruction::SRem,
            Instruction::FRem,
            Instruction::Shl,
            Instruction::LShr,
            Instruction::AShr,
        };
        for (auto code : first_op_zero_sensitive_opcodes)
        {
            if (inst->getOpcode() == code)
            {
                return true;
            }
        }
    }
    return false;
}
InstState directStatePropagation(llvm::Value *u, InstState state, llvm::Value *v)
{
    auto v_inst = llvm::cast<llvm::Instruction>(v);
    if (state.isa(InstState::Zero))
    {
        if (isFullZeroSensitive(v_inst))
        {
            return InstState(InstState::Zero);
        }
        for (auto i = 0u; i < v_inst->getNumOperands(); ++i)
        {
            if (v_inst->getOperand(i) == u && isPartialZeroSensitive(v_inst, i))
            {
                return InstState(InstState::Zero);
            }
        }

        if (auto call = dyn_cast<CallInst>(v))
        {
            my_dbg() << "enter call inst branch\n";
            if (call->getType()->isVectorTy())
            {
                return InstState(InstState::Unknown);
            }
            auto effects = call->getFunction()->getMemoryEffects();
            my_dbg() << "call: " << *call << " is effective: " << isEffectiveCall(call) << " " << effects << " "
                     << effects.doesNotAccessMemory() << " " << effects.onlyReadsMemory() << "\n";

            if (call->getNumOperands() != 2 || isEffectiveCall(call))
            {
                return InstState(InstState::Unknown);
            }
            // if (call->getArgOperand(0) != u)
            // {
            //     return InstState(InstState::Unknown);
            // }
            LLVMContext &context = v->getContext();
            my_dbg() << "function type: " << *call->getFunctionType() << "\n";
            my_dbg() << "u: " << *u << "\n";
            my_dbg() << "v: " << *v << "\n";
            if (!call->getCalledFunction() || !call->getCalledFunction()->getName().starts_with("llvm."))
            {
                return InstState(InstState::Unknown);
            }

            auto module = std::make_unique<Module>("", context);
            auto ret_type = call->getFunctionType()->getReturnType();
            auto func_type = FunctionType::get(ret_type, false);
            auto func = Function::Create(func_type, Function::ExternalLinkage, "func", module.get());

            auto entry = BasicBlock::Create(context, "entry", func);
            auto arg_type = u->getType();
            if (arg_type->isVectorTy())
            {
                return InstState(InstState::Unknown);
            }
            my_dbg() << "arg type: " << *arg_type << "\n";
            Value *zero_value;
            if (u->getType()->isIntegerTy())
            {
                zero_value = ConstantInt::get(arg_type, 0);
            }
            else
            {
                zero_value = ConstantFP::get(arg_type, 0);
            }
            auto jit_call = CallInst::Create(call->getCalledFunction(), zero_value, "jit_call", entry);
            auto ret = ReturnInst::Create(context, jit_call, entry);
            auto jit = orc::LLJITBuilder().create();
            if (!jit)
            {
                throw jit.takeError();
            }
            if (auto err =
                    jit.get()->addIRModule(orc::ThreadSafeModule(std::move(module), std::make_unique<LLVMContext>())))
            {
                throw err;
            }
            auto sym = cantFail(jit.get()->lookup("func"));
            auto *fnPtr = (float (*)())sym.getValue();
            auto res = fnPtr();
            if (res == 0)
            {
                return InstState(InstState::Zero);
            }
            else
            {
                return InstState(res);
            }
        }
        return InstState(InstState::Unknown);
    }
    else if (state.isa(InstState::Constant))
    {
    }
    return InstState(InstState::Unknown);
}

InstState directUnaryStatePropagation(llvm::Value *u, InstState state, llvm::Value *v)
{
    auto v_inst = cast<Instruction>(v);
    if (state.isa(InstState::Zero))
    {
        if (isFullZeroSensitive(v_inst) || isPartialZeroSensitive(v_inst, 0))
        {
            return InstState(InstState::Zero);
        }
    }
    if (state.isa(InstState::Constant) && v_inst->getOpcode() == Instruction::FNeg)
    {
        return InstState(-state.value.constant_fp);
    }
    if (state.isa(InstState::Constant) && isa<CastInst>(v))
    {
        if (state.is_float)
        {
            return InstState(state.value.constant_fp);
        }
        else
        {
            return InstState(state.value.constant);
        }
    }
    return InstState::Unknown;
}
InstState
directBinaryStatePropagation(llvm::Value *op0, InstState state0, llvm::Value *op1, InstState state1, llvm::Value *v)
{
    auto v_inst = cast<Instruction>(v);
    if (state0.isa(InstState::Zero) && state1.isa(InstState::Zero))
    {
        return InstState(InstState::Zero);
    }
    if (state0.isa(InstState::Zero) || state0.isa(InstState::Constant))
    {
        auto res = directStatePropagation(op0, state0, v);
        if (res != InstState::Unknown)
        {
            return res;
        }
    }

    if (state1.isa(InstState::Zero) || state1.isa(InstState::Constant))
    {
        auto res = directStatePropagation(op1, state1, v);
        if (res != InstState::Unknown)
        {
            return res;
        }
    }

    if (state0.isa(InstState::Zero) && state1.isa(InstState::Constant))
    {
        if (v_inst->getOpcode() == Instruction::Add)
        {
            return InstState(state1.value.constant);
        }
        if (v_inst->getOpcode() == Instruction::FAdd)
        {
            return InstState(state1.value.constant_fp);
        }
        if (v_inst->getOpcode() == Instruction::Sub)
        {
            return InstState(-state1.value.constant);
        }
        if (v_inst->getOpcode() == Instruction::FSub)
        {
            return InstState(-state1.value.constant_fp);
        }
        if (v_inst->getOpcode() == Instruction::Xor)
        {
            return InstState(state1.value.constant);
        }
        return InstState::Unknown;
    }
    if (state1.isa(InstState::Zero) && state0.isa(InstState::Constant))
    {
        if (v_inst->getOpcode() == Instruction::Add)
        {
            return InstState(state0.value.constant);
        }
        if (v_inst->getOpcode() == Instruction::FAdd)
        {
            return InstState(state0.value.constant_fp);
        }
        if (v_inst->getOpcode() == Instruction::Sub)
        {
            return InstState(state0.value.constant);
        }
        if (v_inst->getOpcode() == Instruction::FSub)
        {
            return InstState(state0.value.constant_fp);
        }
        if (v_inst->getOpcode() == Instruction::Xor)
        {
            return InstState(state0.value.constant);
        }
        return InstState::Unknown;
    }

    if (state0.isa(InstState::Constant) && state1.isa(InstState::Constant))
    {
        switch (v_inst->getOpcode())
        {
        case Instruction::Add:
            return InstState(state0.value.constant + state1.value.constant);
        case Instruction::FAdd:
            return InstState(state0.value.constant_fp + state1.value.constant_fp);
        case Instruction::Sub:
            return InstState(state0.value.constant - state1.value.constant);
        case Instruction::FSub:
            return InstState(state0.value.constant_fp - state1.value.constant_fp);
        case Instruction::Mul:
            return InstState(state0.value.constant * state1.value.constant);
        case Instruction::FMul:
            return InstState(state0.value.constant_fp * state1.value.constant_fp);
        case Instruction::UDiv:
            return InstState(state0.value.constant / state1.value.constant);
        case Instruction::SDiv:
            return InstState(state0.value.constant / state1.value.constant);
        case Instruction::FDiv:
            return InstState(state0.value.constant_fp / state1.value.constant_fp);
        case Instruction::URem:
            return InstState(state0.value.constant % state1.value.constant);
        case Instruction::SRem:
            return InstState(state0.value.constant % state1.value.constant);
        case Instruction::FRem:
            return InstState(std::fmod(state0.value.constant_fp, state1.value.constant_fp));
        case Instruction::Shl:
            return InstState(state0.value.constant << state1.value.constant);
        case Instruction::LShr:
            return InstState(state0.value.constant >> state1.value.constant);
        case Instruction::AShr:
            return InstState(state0.value.constant >> state1.value.constant);
        case Instruction::And:
            return InstState(state0.value.constant & state1.value.constant);
        case Instruction::Or:
            return InstState(state0.value.constant | state1.value.constant);
        case Instruction::Xor:
            return InstState(state0.value.constant ^ state1.value.constant);
        default:
            return InstState::Unknown;
        }
    }
    if (state0.isa(InstState::Zero))
    {
        switch (v_inst->getOpcode())
        {
        case Instruction::Add:
        case Instruction::FAdd:
        case Instruction::Or:
            // return InstState(op1);
            my_dbg() << "v at substitute 1: " << *v << "\n";
            my_dbg() << "op1: " << *op1 << "\n";
            return InstState::get_substitute(1);
        }
    }
    if (state1.isa(InstState::Zero))
    {
        switch (v_inst->getOpcode())
        {
        case Instruction::Add:
        case Instruction::FAdd:
        case Instruction::Or:
        case Instruction::Sub:
        case Instruction::FSub:
            // return InstState(op0);
            my_dbg() << "v at substitute 0: " << *v << "\n";
            my_dbg() << "op0: " << *op0 << "\n";
            return InstState::get_substitute(0);
        }
    }
    return InstState::Unknown;
}
InstState storeStatePropogation(size_t u, InstState s, const StatesMap &states, size_t v, const ValueGraph &graph)
{
    auto v_inst = cast<Instruction>(graph[v]);
    if (auto store = dyn_cast<StoreInst>(v_inst))
    {
        for (auto prev = store->getPrevNonDebugInstruction(); prev != nullptr;
             prev = prev->getPrevNonDebugInstruction())
        {
            if (auto load = dyn_cast<LoadInst>(prev))
            {
                if (load->getPointerOperand() == store->getPointerOperand())
                {
                    auto val_state = states(u, s, graph[store->getValueOperand()]);
                    // if (val_state.isa(InstState::Substitute) && val_state.get<Value *>() == load)
                    if (val_state.isa(InstState::Substitute) &&
                        val_state.get_value(graph, store->getValueOperand()) == load)
                    {
                        load->setMetadata("is_substitute", MDNode::get(v_inst->getContext(), {}));
                        my_dbg() << "load: " << *load << "\n";
                        my_dbg() << "substitute: " << *val_state.get_value(graph, store->getValueOperand()) << "\n";
                        my_dbg() << "store propagation: " << *store << "\n";
                        return InstState(InstState::Zero);
                    }
                }
            }

            // if (auto call = dyn_cast<CallInst>(prev))
            // {
            //     my_dbg() << "call in store propagation: " << *call << "\n";
            // }
            if (isa<CallInst, InvokeInst>(prev) && !is_instrument(prev))
            {
                return InstState(InstState::Unknown);
            }
        }
    }
    return InstState::Unknown;
}
/**
 * @brief This function need to be called in topo-order, or it will miss some information.
 * Evaluate the state of v based on the states of its operands when u is zero.
 * @param states 
 * @param v 
 * @param graph 
 * @return InstState 
 */
InstState statePropagation(size_t u,
                           InstState s,
                           const StatesMap &states,
                           size_t v,
                           const ValueGraph &graph,
                           PropagationFuncInfo &propagation_func_info)
{
    static char *ZERO_SPEC_JIT = getenv("ZERO_SPEC_JIT");
    my_dbg() << "evaluate u: " << u << " " << *graph[u] << "\n";
    auto v_inst = cast<Instruction>(graph[v]);
    if (isa<PHINode>(v_inst))
    {
        return InstState(InstState::Unknown);
    }
    if (v_inst->getType()->isPointerTy())
    {
        return InstState(InstState::Unknown);
    }
    if (auto call = dyn_cast<CallInst>(v_inst); call && call->getCalledFunction())
    {
        // my_dbg() << "call: " << *call << "\n";
        my_dbg() << "called func: " << *call->getCalledFunction() << "\n";
        // my_dbg() << call->getCalledFunction()->getMemoryEffects() << "\n";
        // my_dbg() << call->getCalledFunction()->getMemoryEffects().doesNotAccessMemory() << "\n";
        // my_dbg() << call->getCalledFunction()->hasFnAttribute("willreturn") << "\n";
        if (ZERO_SPEC_JIT)
        {
            if (call->getCalledFunction()->getName().starts_with("llvm.") &&
                call->getCalledFunction()->getMemoryEffects().doesNotAccessMemory())
            {
                testFunction(*call->getCalledFunction());
            }
        }
        my_dbg() << "func name:" << call->getCalledFunction()->getName() << "\n";
        if (auto iter = propagation_func_info.find(call->getCalledFunction()->getName().str());
            iter != propagation_func_info.end())
        {
            // my_dbg() << "propagation func: " << call->getCalledFunction()->getName() << "\n";
            if (s.isa(InstState::Zero))
            {
                for (auto [i, arg] : llvm::enumerate(call->args()))
                {
                    // if (arg.get() == graph[u])
                    if (states(u, InstState::Zero, graph[arg.get()]).isa(InstState::Zero))
                    {
                        if (iter->second[i] == -2)
                        {
                            return InstState(InstState::Unknown);
                        }
                        else if (iter->second[i] == -1)
                        {
                            return InstState(InstState::Zero);
                        }
                        else
                        {
                            // return InstState(call->getArgOperand(iter->second[i]));
                            return InstState::get_substitute(iter->second[i]);
                        }
                    }
                }
            }
        }

        if (call->getNumOperands() != 2)
        {
            return InstState(InstState::Unknown);
        }
        auto w = graph[call->getArgOperand(0)];
        my_dbg() << "propagate func: " << states(u, s, w).isa(InstState::Zero) << "\n";
        return directStatePropagation(call->getArgOperand(0), states(u, s, w), call);
    }
    if (auto call = dyn_cast<InvokeInst>(v_inst))
    {
        if (call->getNumOperands() != 2)
        {
            return InstState(InstState::Unknown);
        }
        auto w = graph[call->getArgOperand(0)];
        return directStatePropagation(call->getArgOperand(0), states(u, s, w), call);
    }
    if (v_inst->getNumOperands() == 1)
    {
        auto w = graph[v_inst->getOperand(0)];
        auto res = directUnaryStatePropagation(v_inst->getOperand(0), states(u, s, w), v_inst);
        if (res != InstState::Unknown)
        {
            return res;
        }
        res = directStatePropagation(v_inst->getOperand(0), states(u, s, w), v_inst);
    }
    if (v_inst->getNumOperands() == 2)
    {
        // my_dbg() << "-------------\n";
        // my_dbg() << "u: " << u << " " << *graph[u] << "\n";
        // my_dbg() << "op0 id: " << graph[v_inst->getOperand(0)] << "\n";
        // my_dbg() << "op1 id: " << graph[v_inst->getOperand(1)] << "\n";
        // my_dbg() << *v_inst->getOperand(0) << "\n"
        //        << states(u, s, graph[v_inst->getOperand(0)]).state << "\n"
        //        << *v_inst->getOperand(1) << "\n"
        //        << states(u, s, graph[v_inst->getOperand(1)]).state << "\n"
        //        << *v_inst << "\n";
        auto res = directBinaryStatePropagation(v_inst->getOperand(0),
                                                states(u, s, graph[v_inst->getOperand(0)]),
                                                v_inst->getOperand(1),
                                                states(u, s, graph[v_inst->getOperand(1)]),
                                                v_inst);
        if (res != InstState::Unknown)
        {
            return res;
        }
        res = storeStatePropogation(u, s, states, v, graph);
        if (res != InstState::Unknown)
        {
            return res;
        }
    }
    return InstState::Unknown;
}

using namespace llvm;
using std::vector;

AnalysisKey ZeroBenefitAnalysis::Key;
bool isEffective(Value *v)
{
    if (is_instrument(v))
    {
        return false;
    }
    if (isa<Instruction>(v))
    {
        if (isa<StoreInst, CallInst, ReturnInst, InvokeInst, PHINode, BranchInst>(v))
        {
            return true;
        }
    }
    return false;
}

bool isCall(Value *v) { return isa<CallInst, InvokeInst>(v); }

bool hasEffectiveCallForSC(int sc_label, const ValueGraph &graph)
{
    for (auto v : graph.sc_label2id_map()[sc_label])
    {
        if (isEffectiveCall(graph[v]))
        {
            return true;
        }
    }
    return false;
}

bool isEffectiveForSC(int sc_label, const ValueGraph &graph)
{
    for (auto v : graph.sc_label2id_map()[sc_label])
    {
        if (isEffective(graph[v]))
        {
            return true;
        }
    }
    return false;
}

void partialDeadCodeSearch(const DominanceInfo &dom_info,
                           const StatesMap &states,
                           const std::vector<std::vector<unsigned>> &direct_dead_vertex,
                           const ValueGraph &graph,
                           std::vector<std::vector<unsigned>> &indirect_dead_vertex)
{
    for (const auto [u_in_graph, propagated_insts] : llvm::enumerate(direct_dead_vertex))
    {
        auto u_val = graph[u_in_graph];
        // id of dom_info
        std::set<unsigned> valid_dominance_frontiers;
        std::set<unsigned> dead_dominance_frontiers;
        // id of dom_info
        std::unordered_map<unsigned, unsigned> count_map;
        std::set<unsigned> dead_code_set;
        std::vector<unsigned> dominators = propagated_insts;
        std::vector<char> processed = std::vector<char>(dom_info.get_graph().getGraph().m_vertices.size(), 0);
        while (!dominators.empty())
        {
            valid_dominance_frontiers.clear();
            dead_dominance_frontiers.clear();
            for (auto v_graph : dominators)
            {
                auto v_val = graph[v_graph];
                auto v_inst = cast<Instruction>(v_val);
                auto df_v = dom_info.getDomFrontier(v_inst);
                for (auto w_dom : df_v)
                {
                    count_map[w_dom]++;
                }
            }
            for (auto [w_dom, count] : count_map)
            {
                if (count > 1)
                {
                    valid_dominance_frontiers.insert(w_dom);
                }
            }

            for (auto w_dom : valid_dominance_frontiers)
            {
                bool is_dead = true;
                my_dbg() << "w_dom: " << w_dom << " " << *dom_info[w_dom] << "\n";
                for (auto p_val : dom_info[w_dom]->users())
                {
                    if (is_instrument(p_val) || !isa<Instruction, Argument>(p_val))
                    {
                        continue;
                    }
                    if (isa<UserOp2Inst>(p_val))
                    {
                        continue;
                    }
                    bool is_dominated = false;
                    for (auto v_graph : dominators)
                    {
                        auto v_val = graph[v_graph];
                        if (is_instrument(v_val) || !isa<Instruction, Argument>(v_val))
                        {
                            continue;
                        }
                        if (dom_info.dom(v_val, p_val))
                        {
                            auto v_state = states(u_in_graph, InstState::Zero, v_graph);
                            if (v_state.isa(InstState::Substitute))
                            {
                                // if (!graph.contains(v_state.get<Value *>()))
                                if (!graph.contains(v_state.get_value(graph, graph[v_graph])))
                                {
                                    my_dbg()
                                        // << "subsutitute inst for v: " << *v_state.get<Value *>() << " not in graph\n";
                                        << "subsutitute inst for v: " << *v_state.get_value(graph, v_graph)
                                        << " not in graph\n";
                                }
                            }
                            // if (!v_state.isa(InstState::Substitute) ||
                            //     (isa<Instruction, Argument>(v_state.get<Value *>()) &&
                            //      !graph.reachable(p_val, v_state.get<Value *>())))
                            if (!v_state.isa(InstState::Substitute) ||
                                (isa<Instruction, Argument>(v_state.get_value(graph, v_graph)) &&
                                 !graph.reachable(p_val, v_state.get_value(graph, v_graph))))
                            {
                                is_dominated = true;
                                break;
                            }
                        }
                    }
                    if (!is_dominated)
                    {
                        is_dead = false;
                        break;
                    }
                }
                if (is_dead)
                {
                    dead_dominance_frontiers.insert(w_dom);
                }
            }
            // insert valid dominance frontiers to dominators
            dominators.clear();
            for (auto w_dom : dead_dominance_frontiers)
            {
                if (!processed[w_dom])
                {
                    dominators.push_back(w_dom);
                    processed[w_dom] = 1;
                    for (unsigned i = 0; i < dom_info.get_graph().getGraph().m_vertices.size(); ++i)
                    {
                        if (dom_info.dom(dom_info[w_dom], dom_info[i]))
                        {
                            dead_code_set.insert(i);
                        }
                    }
                }
            }
        }
        for (auto dead_code : dead_code_set)
        {
            indirect_dead_vertex[u_in_graph].push_back(graph[dom_info.get_graph()[dead_code]]);
        }
    }
}

void subtree(const DominanceInfo &dom_info,
             const ValueGraph &graph,
             const std::set<Value *> live_nodes,
             const std::unordered_set<int> &input,
             std::unordered_set<int> &output,
             int u_in_graph,
             Value *zero_value_inst)
{
    for (auto v_dom : dom_info.get_idomed_by(dom_info[graph[u_in_graph]]))
    {
        auto v_in_graph = graph[dom_info[v_dom]];
        bool is_live = false;
        for (auto live_node : live_nodes)
        {
            if (graph.reachable(dom_info[v_dom], live_node))
            {
                is_live = true;
                break;
            }
        }
        if (is_live)
        {
            continue;
        }
        if (!graph.reachable(dom_info[v_dom], zero_value_inst))
        {
            if (input.find(v_in_graph) == input.end() && output.find(v_in_graph) == output.end())
            {
                if (isEffective(graph[v_in_graph]))
                {
                    my_dbg() << "effective inst in subtree: " << *graph[v_in_graph] << "\n";
                    my_dbg() << "u: " << *graph[u_in_graph] << "\n";
                }
                my_dbg() << "insert w into subtree: " << *graph[v_in_graph] << "\n";
                my_dbg() << "insert w by u: " << *graph[u_in_graph] << "\n";
                output.insert(v_in_graph);
                subtree(dom_info, graph, live_nodes, input, output, v_in_graph, zero_value_inst);
            }
        }
    }
}
void subtree2(const DominanceInfo &dom_info,
              const ValueGraph &graph,
              const std::set<Value *> live_nodes,
              const std::unordered_set<int> &input,
              std::unordered_set<int> &output,
              int u_in_graph,
              Value *zero_value_inst)
{
    std::vector<int> stack;
    stack.push_back(u_in_graph);
    while (!stack.empty())
    {
        auto u_in_graph = stack.back();
        stack.pop_back();
        for (auto v_dom : dom_info.get_idomed_by(dom_info[graph[u_in_graph]]))
        {
            auto v_in_graph = graph[dom_info[v_dom]];
            bool is_live = false;
            for (auto live_node : live_nodes)
            {
                if (graph.reachable(dom_info[v_dom], live_node))
                {
                    is_live = true;
                    break;
                }
            }
            if (is_live)
            {
                continue;
            }
            if (!graph.reachable(dom_info[v_dom], zero_value_inst))
            {
                if (input.find(v_in_graph) == input.end() && output.find(v_in_graph) == output.end())
                {
                    // if (isEffective(graph[v_in_graph]))
                    // {
                    //     my_dbg() << "effective inst in subtree: " << *graph[v_in_graph] << "\n";
                    //     my_dbg() << "u: " << *graph[u_in_graph] << "\n";
                    // }
                    // my_dbg() << "insert w into subtree: " << *graph[v_in_graph] << "\n";
                    // my_dbg() << "insert w by u: " << *graph[u_in_graph] << "\n";
                    output.insert(v_in_graph);
                    stack.push_back(v_in_graph);
                }
            }
        }
    }
}

std::pair<int, User *> get_unique_valid_user(Value *v)
{
    User *res = nullptr;
    int count = 0;
    for (auto user : v->users())
    {
        if (!is_instrument(user) && !isa<UserOp1Inst, UserOp2Inst>(user))
        {
            count++;
            res = user;
        }
    }
    return {count, res};
}
void partialDeadCodeSearch2(const DominanceInfo &dom_info,
                            const StatesMap &states,
                            const std::vector<std::vector<unsigned>> &direct_dead_vertex,
                            const ValueGraph &graph,
                            std::vector<std::vector<unsigned>> &indirect_dead_vertex)
{
    for (const auto [u_in_graph, propagated_insts] : llvm::enumerate(direct_dead_vertex))
    {
        auto u_val = graph[u_in_graph];
        unordered_set<int> processed;
        unordered_map<int, unordered_set<int>> dom_map;
        unordered_set<int> backward_slicings;
        auto di = propagated_insts;

        my_dbg() << "search partial dead code for: " << *u_val << "\n";

        std::set<llvm::Value *> live_nodes;
        for (auto v_in_graph : propagated_insts)
        {
            auto s = states(u_in_graph, InstState::Zero, v_in_graph);
            if (s.isa(InstState::Substitute))
            {
                auto w_inst = dyn_cast<Instruction>(s.get_value(graph, graph[v_in_graph]));
                if (w_inst && !w_inst->hasMetadata("is_substitute"))
                {
                    live_nodes.insert(w_inst);
                    my_dbg() << "live node: " << *w_inst << "\n";
                }
                else if (w_inst && w_inst->hasMetadata("is_substitute"))
                {
                    auto [use_count, unique_user] = get_unique_valid_user(w_inst);
                    if (use_count > 1)
                    {
                        live_nodes.insert(w_inst);
                        my_dbg() << "live node: " << *w_inst << "\n";
                    }
                    else if (use_count == 1)
                    {
                        auto [_use_count, _unique_user] = get_unique_valid_user(unique_user);
                        if (!(_use_count == 1 && isa<StoreInst>(_unique_user)))
                        {
                            live_nodes.insert(w_inst);
                        }
                    }
                }
            }
        }
        // vector<int> d0;
        // for (auto v: di)
        // {
        //     bool valid = true;
        //     for (auto p: di)
        //     {
        //         if (v != p)
        //         {
        //             if (dom_info.dom(dom_info[p], dom_info[v]))
        //             {
        //                 valid = false;
        //                 break;
        //             }
        //         }
        //     }
        //     if (valid)
        //     {
        //         d0.push_back(v);
        //     }
        // }
        // int round = 0;
        while (!di.empty())
        {
            // fprintf(stderr, "round: %d\n", round++);
            vector<unsigned int> di_next;
            std::set<unsigned int> di_in_dom;
            // di_in_dom.reserve(di.size());

            for (auto d_in_graph : di)
            {
                auto d_in_dom = dom_info[graph[d_in_graph]];
                if (d_in_dom != -1ul)
                {
                    di_in_dom.insert(d_in_dom);
                }
            }
            for (auto d_in_graph : di)
            {
                if (processed.find(d_in_graph) != processed.end())
                {
                    continue;
                }
                processed.insert(d_in_graph);
                auto d_val = graph[d_in_graph];
                for (auto w_dom : dom_info.getDomFrontier(d_val))
                {
                    auto &dom_map_for_w = dom_map[w_dom];
                    auto w_val = dom_info[w_dom];
                    if (isEffective(w_val))
                    {
                        continue;
                    }
                    bool is_live = false;

                    for (auto live_node : live_nodes)
                    {
                        if (graph.reachable(w_val, live_node))
                        {
                            is_live = true;
                            break;
                        }
                    }
                    if (is_live)
                    {
                        continue;
                    }
                    unordered_set<int> user_set;
                    for (auto v_user : w_val->users())
                    {
                        auto v_dom = dom_info[v_user];
                        auto v_in_graph = graph[v_user];
                        if (v_dom == -1ul)
                        {
                            continue;
                        }
                        user_set.insert(v_dom);
                        if (dom_map_for_w.find(v_dom) != dom_map_for_w.end())
                        {
                            continue;
                        }
                        auto parent = dom_info.parent(v_dom);
                        while (parent != 0)
                        {
                            if (dom_map_for_w.find(parent) != dom_map_for_w.end())
                            {
                                dom_map_for_w.insert(v_dom);
                                break;
                            }
                            parent = dom_info.parent(parent);
                        }
                        // for (auto p_dom : di_in_dom)
                        // {
                        //     if (dom_info.dom(p_dom, v_dom))
                        //     {
                        //         dom_map_for_w.insert(v_dom);
                        //         break;
                        //     }
                        // }
                    }
                    if (dom_map_for_w.size() == user_set.size() && !graph.reachable(w_val, u_val))
                    {
                        if (isEffective(w_val))
                        {
                            my_dbg() << "effective inst: " << *dom_info[w_dom] << "\n";
                            my_dbg() << "di: " << *d_val << "\n";
                        }
                        my_dbg() << "insert w into di_next: " << *w_val << "\n";
                        my_dbg() << "w is inserted by: " << *d_val << "\n";
                        di_next.push_back(graph[w_val]);
                    }
                }
            }

            for (auto d : di)
            {
                backward_slicings.insert(d);
                my_dbg() << "insert d into backward_slicings: " << *graph[d] << "\n";
            }
            di = std::move(di_next);
        }
        // for (auto d : backward_slicings)
        // {
        //     if (isEffective(graph[d]))
        //     {
        //         my_dbg() << "effective inst in backward_slicings: " << *graph[d] << "\n";
        //         my_dbg() << "u: " << *graph[u_in_graph] << "\n";
        //     }
        // }
        unordered_set<int> subtree_backward_slicings;
        for (auto d : backward_slicings)
        {
            subtree(dom_info, graph, live_nodes, backward_slicings, subtree_backward_slicings, d, u_val);
        }
        indirect_dead_vertex[u_in_graph].insert(
            indirect_dead_vertex[u_in_graph].end(), backward_slicings.begin(), backward_slicings.end());

        indirect_dead_vertex[u_in_graph].insert(
            indirect_dead_vertex[u_in_graph].end(), subtree_backward_slicings.begin(), subtree_backward_slicings.end());
    }
}

void partialDeadCodeSearch3(const DominanceInfo &dom_info,
                            const StatesMap &states,
                            const std::vector<std::vector<unsigned>> &direct_dead_vertex,
                            const ValueGraph &graph,
                            std::vector<std::vector<unsigned>> &indirect_dead_vertex)
{
    for (const auto [u_in_graph, propagated_insts] : llvm::enumerate(direct_dead_vertex))
    {
        if (propagated_insts.size() == 0)
        {
            continue;
        }
        auto u = graph[u_in_graph];
        ValueGraph merged_graph;
        for (int i = 0; i < graph.getGraph().m_vertices.size(); ++i)
        {
            merged_graph.addVertex(graph[i]);
            for (auto e : to_range(boost::out_edges(i, graph.getGraph())))
            {
                if (std::find(direct_dead_vertex[u_in_graph].begin(),
                              direct_dead_vertex[u_in_graph].end(),
                              boost::source(e, graph.getGraph())) != direct_dead_vertex[u_in_graph].end())
                {
                    merged_graph.addEdge(u_in_graph, boost::target(e, graph.getGraph()));
                }
            }
        }
        DominanceInfo merged_dom_info(merged_graph);
        for (auto v_in_dom : merged_dom_info.children(merged_dom_info[u]))
        {
            auto v_in_graph = graph[merged_dom_info[v_in_dom]];
            indirect_dead_vertex[u_in_graph].push_back(v_in_graph);
        }
    }
}
void buildFullGraph(Function &F, ValueGraph &graph)
{
    for (auto &args : F.args())
    {
        // if (!args.getType()->isPointerTy())
        {
            graph.addVertex(&args);
        }
    }
    for (auto &bb : F)
    {
        for (auto &inst : bb)
        {
            my_dbg() << "inst: " << inst << "\n";
            if (auto call = dyn_cast<CallInst>(&inst))
            {
                auto callee = call->getCalledFunction();
                if (callee &&
                    (callee->getName().starts_with("llvm.dbg") || callee->getName().starts_with("llvm.lifetime") ||
                     callee->getName().starts_with(INSTRUMENTATION_PREFIX_STR)))
                {
                    continue;
                }
            }
            graph.addVertex(&inst);
        }
    }
    for (auto &bb : F)
    {
        for (auto &inst : bb)
        {
            // for (auto user : inst.users())
            // {
            //     if (auto *userInst = dyn_cast<Instruction>(user))
            //     {
            //         if (graph.contains(userInst))
            //         {
            //             graph.addEdge(&inst, userInst);
            //         }
            //     }
            // }
            for (auto &operand : inst.operands())
            {
                if (graph.contains(operand.get()) && graph.contains(&inst))
                {
                    graph.addEdge(operand.get(), &inst);
                }
            }
        }
    }
}
void ZeroBenefitAnalysis::buildGraph(Function &F, ValueGraph &graph)
{
    ValueGraph reverseGraph;
    vector<Value *> effectiveValues;
    for (auto &args : F.args())
    {
        if (!args.getType()->isPointerTy())
        {
            reverseGraph.addVertex(&args);
            effectiveValues.push_back(&args);
        }
    }

    for (auto &bb : F)
    {
        for (auto &inst : bb)
        {
            // my_dbg() << "inst: " << inst << "\n";
            if (auto call = dyn_cast<CallInst>(&inst))
            {
                auto callee = call->getCalledFunction();
                if (callee &&
                    (callee->getName().starts_with("llvm.dbg") || callee->getName().starts_with("llvm.lifetime") ||
                     callee->getName().starts_with(INSTRUMENTATION_PREFIX_STR)))
                {
                    continue;
                }
            }
            if (!inst.getType()->isPointerTy() || isa<CallInst>(&inst))
            {
                reverseGraph.addVertex(&inst);
            }

            if (isEffective(&inst))
            {
                effectiveValues.push_back(&inst);
            }
        }
    }

    for (auto &bb : F)
    {
        for (auto &inst : bb)
        {
            for (auto user : inst.users())
            {
                if (auto *userInst = dyn_cast<Instruction>(user))
                {
                    if (reverseGraph.contains(userInst))
                    {
                        reverseGraph.addEdge(userInst, &inst);
                    }
                }
            }
        }
    }
    // dump reverseGraph
    // for (auto v : reverseGraph.value_range())
    // {
    //     my_dbg() << "reverseGraph: " << *v << "\n";
    //     if (isa<Instruction>(v))
    //     {
    //         my_dbg() << "function: " << *cast<Instruction>(v)->getParent()->getParent() << "\n";
    //     }
    //     for (auto user : v->users())
    //     {
    //         my_dbg() << "user: " << *user << "\n";
    //     }
    // }

    // as we remove pointer type values, there may be some values that are not reachable to the effective values,
    // so remove them
    // auto visited = std::make_unique<bool[]>(boost::num_vertices(reverseGraph.getGraph()));
    auto visited = new bool[boost::num_vertices(reverseGraph.getGraph())];
    memset(visited, 0, boost::num_vertices(reverseGraph.getGraph()));
    vector<ValueGraph::VertexProperty> effectiveReachableValues = effectiveValues;
    for (auto &value : effectiveValues)
    {
        if (reverseGraph[value] == -1ul)
        {
            continue;
        }
        if (!visited[reverseGraph[value]])
        {
            vector<ValueGraph::vertex_t> stack;
            stack.push_back(reverseGraph[value]);
            while (!stack.empty())
            {
                auto vertex = stack.back();
                stack.pop_back();
                if (vertex == -1ul)
                {
                    continue;
                }
                visited[vertex] = true;
                // for (auto [begin, end] = boost::adjacent_vertices(vertex, reverseGraph.getGraph()); begin != end;
                //      ++begin)
                my_dbg() << "vertex: " << vertex << "\n";
                for (auto e : to_range(boost::out_edges(vertex, reverseGraph.getGraph())))
                {
                    // auto target = *begin;
                    auto target = boost::target(e, reverseGraph.getGraph());
                    my_dbg() << "target: " << target << " vertex num: " << boost::num_vertices(reverseGraph.getGraph())
                             << "\n";
                    if (!visited[target])
                    {
                        stack.push_back(target);
                        effectiveReachableValues.push_back(reverseGraph[target]);
                        visited[target] = true;
                    }
                }
            }
        }
    }

    for (auto &value : effectiveReachableValues)
    {
        graph.addVertex(value);
    }
    for (auto &value : effectiveReachableValues)
    {
        for (auto user : value->users())
        {
            // TODO: add Constant support
            if (auto *userInst = dyn_cast<Instruction>(user))
            {
                if (graph.contains(userInst))
                {
                    graph.addEdge(value, userInst);
                }
            }
        }
    }
    // dump graph
    // for (auto v : graph.value_range())
    // {
    //     my_dbg() << "graph: " << *v << "\n";
    //     for (auto user : v->users())
    //     {
    //         my_dbg() << "user: " << *user << "\n";
    //     }
    // }

    graph.build_scc();

    // dump sc_graph
    // for (auto [i, v] : llvm::enumerate(graph.sc_label2id_map()))
    // {
    // my_dbg() << "sc_graph for " << i << ": ";
    // for (auto id : v)
    // {
    //     my_dbg() << *graph[id] << ";";
    // }
    // my_dbg() << "\n";
    // }

    delete[] visited;
}

void cutBackEdge(const ValueGraph &graph, ValueGraph &dag, LoopInfo &loopInfo)
{
    dag = graph;
    for (auto val : graph.value_range())
    {
        auto inst = dyn_cast<Instruction>(val);
        if (!inst)
        {
            continue;
        }
        auto loop = loopInfo.getLoopFor(inst->getParent());
        if (!loop)
        {
            continue;
        }
        auto preheader = loop->getLoopPreheader();
        auto header = loop->getHeader();
        for (auto &phi : header->phis())
        {
            for (auto &op : phi.operands())
            {
                if (auto opInst = dyn_cast<Instruction>(op.get()))
                {
                    if (opInst->getParent() != preheader)
                    {
                        dag.removeEdge(val, &phi);
                    }
                }
            }
        }
        for (auto user : inst->users())
        {
            auto userInst = dyn_cast<Instruction>(user);
            if (!userInst)
            {
                continue;
            }
            if (loop->contains(userInst))
            {
                dag.removeEdge(userInst, val);
            }
        }
    }
}

void buildEffectiveGraph(const ValueGraph &graph, ValueGraph &effective_graph)
{
    unsigned effective_id = -1;
    llvm::Instruction *super_effective_inst = UserOp1Inst::Create(graph[0ul]->getContext());
    effective_graph.addVertex(super_effective_inst);
    for (auto [i, v] : llvm::enumerate(graph.value_range()))
    {
        if (!is_instrument(v))
        {
            effective_graph.addVertex(v);
        }
        if (isEffective(v))
        {
            effective_graph.addEdge(super_effective_inst, v);
        }
    }
    for (auto edge : graph.getGraph().m_edges)
    {
        auto source_v = graph[edge.m_source];
        auto target_v = graph[edge.m_target];
        if (effective_graph.contains(source_v) && effective_graph.contains(target_v))
        {
            effective_graph.addEdge(target_v, source_v);
            my_dbg() << "edge: " << *source_v << " -> " << *target_v << "\n";
        }
    }
}

ZeroBenefitAnalysisResult ZeroBenefitAnalysis::run(Function &F, FunctionAnalysisManager &AM)
{
    ValueGraph graph;
    buildFullGraph(F, graph);
    for (auto [i, v] : llvm::enumerate(graph.value_range()))
    {
        my_dbg() << "node: " << i << ": " << *v << "\n";
    }
    for (auto edges : graph.getGraph().m_edges)
    {
        my_dbg() << "edge: " << edges.m_source << " -> " << edges.m_target << "\n";
    }

    ValueGraph dag_with_backedge;
    auto &loopInfo = AM.getResult<LoopAnalysis>(F);
    cutBackEdge(graph, dag_with_backedge, loopInfo);
    auto vertex_num = boost::num_vertices(dag_with_backedge.getGraph());
    // necessary matrix
    // auto N_ptr = std::make_unique<bool[]>(vertex_num * vertex_num);
    // memset(N_ptr.get(), 0, vertex_num * vertex_num * sizeof(bool));
    // auto N = span2d<bool>(N_ptr.get(), vertex_num, vertex_num);
    // auto N_visited_ptr = std::make_unique<bool[]>(vertex_num * vertex_num);
    // memset(N_visited_ptr.get(), 0, vertex_num * vertex_num * sizeof(bool));
    // auto N_visited = span2d<bool>(N_visited_ptr.get(), vertex_num, vertex_num);
    // auto sc_vertex_num = boost::num_vertices(graph.getSCGraph());
    // auto N_SC_ptr = std::make_unique<bool[]>(sc_vertex_num * sc_vertex_num);
    // memset(N_SC_ptr.get(), 0, sc_vertex_num * sc_vertex_num * sizeof(bool));
    // auto N_SC = span2d<bool>(N_SC_ptr.get(), sc_vertex_num, sc_vertex_num);
    // auto sc_node_degrees = std::make_unique<int[]>(sc_vertex_num);

    auto propagation_func_info = loadPropagationFuncInfo();

    // TODO: This algorithm is not best.
    // For A -> B -> C, N(A, C) == N(A, B), but this algorithm doesn't consider this.
    // for (auto v = 0u; v < sc_vertex_num; ++v)
    // {
    //     if (isEffectiveForSC(v, graph))
    //     {
    //         continue;
    //     }
    //     vector<int> ready;
    //     for (auto u = 0u; u < sc_vertex_num; ++u)
    //     {
    //         sc_node_degrees[u] = boost::out_degree(u, graph.getSCGraph());
    //         // my_dbg() << "out degree of " << u << ": " << sc_node_degrees[u] << "\n";
    //     }
    //     ready.push_back(v);
    //     while (!ready.empty())
    //     {
    //         auto target = ready.back();
    //         ready.pop_back();

    //         for (auto e : to_range(boost::in_edges(target, graph.getSCGraph())))
    //         {
    //             auto u = boost::source(e, graph.getSCGraph());
    //             if (hasEffectiveCallForSC(v, graph))
    //             {
    //                 continue;
    //             }

    //             sc_node_degrees[u]--;
    //             my_dbg() << "cut from v " << v << ", out degree of " << u << ": " << sc_node_degrees[u] << "\n";
    //             if (sc_node_degrees[u] == 0 && !isEffectiveForSC(u, graph))
    //             {
    //                 N_SC(u, v) = true;
    //                 ready.push_back(u);
    //             }
    //         }
    //     }
    // }
    // dump N_SC
    // for (auto u = 0u; u < sc_vertex_num; ++u)
    // {
    //     for (auto v = 0u; v < sc_vertex_num; ++v)
    //     {
    //         if (N_SC(u, v))
    //         {
    //             my_dbg() << "N_SC(" << u << ", " << v << ")\n";
    //         }
    //     }
    // }

    // FIXME: N_SC actually is N(U_sc, V_sc), but what we need is N(U_sc, v).
    // Currently we just skip if V_sc contains more than one node.
    // for (auto v_sc = 0u; v_sc < sc_vertex_num; ++v_sc)
    // {
    //     if (graph.sc_label2id_map()[v_sc].size() != 1)
    //     {
    //         continue;
    //     }
    //     for (auto u_sc = 0u; u_sc < sc_vertex_num; ++u_sc)
    //     {
    //         if (u_sc == v_sc)
    //         {
    //             continue;
    //         }
    //         if (N_SC(u_sc, v_sc))
    //         {
    //             for (auto u : graph.sc_label2id_map()[u_sc])
    //             {
    //                 for (auto v : graph.sc_label2id_map()[v_sc])
    //                 {
    //                     my_dbg() << "u_sc " << u_sc << " -> " << *graph[u] << ", v_sc " << v_sc << " -> " << *graph[v]
    //                            << "\n";
    //                     N(u, v) = true;
    //                 }
    //             }
    //         }
    //     }
    // }
    // my_dbg() << "vertex num: " << vertex_num << "\n";
    // // dump N
    // for (auto u = 0u; u < vertex_num; ++u)
    // {
    //     for (auto v = 0u; v < vertex_num; ++v)
    //     {
    //         if (N(u, v))
    //         {
    //             my_dbg() << "N([" << *graph[u] << "], [" << *graph[v] << "]) = " << N(u, v) << "\n";
    //         }
    //     }
    // }

    // reachability matrix
    // auto reachability_ptr = std::make_unique<bool[]>(vertex_num * vertex_num);
    // memset(reachability_ptr.get(), 0, vertex_num * vertex_num * sizeof(bool));
    // auto reachability0 = span2d<bool>(reachability_ptr.get(), vertex_num, vertex_num);
    // // vector<int> reachability(vertex_num * vertex_num);
    // ValueGraph::Graph closure;
    // boost::transitive_closure(dag_with_backedge.getGraph(), closure);
    // for (size_t u = 0; u < vertex_num; ++u)
    // {
    //     for (auto e : to_range(boost::out_edges(u, closure)))
    //     {
    //         auto v = boost::target(e, closure);
    //         if (u != v)
    //         {
    //             reachability0(u, v) = 1;
    //         }
    //     }
    // }
    auto *TIRA = &AM.getResult<TargetIRAnalysis>(F);
    auto *loop_info = &AM.getResult<LoopAnalysis>(F);
    // for (auto &bb : F)
    // {
    //     for (auto &inst : bb)
    //     {
    //         for (auto &op : inst.operands())
    //         {
    //             auto res = directStatePropagation(op.get(), InstState(InstState::Zero), &inst);
    //             if (res.isa(InstState::Zero))
    //             {
    //                 my_dbg() << "---------Zero---------\n";
    //                 my_dbg() << *op.get() << " ---> " << inst << "\n";
    //                 my_dbg() << "overhead of inst: " << TIRA->getInstructionCost(&inst, TargetTransformInfo::TCK_Latency)
    //                        << "\n";
    //             }
    //         }
    //     }
    // }

    // dump reachability0
    // for (auto u = 0u; u < vertex_num; ++u)
    // {
    //     for (auto v = 0u; v < vertex_num; ++v)
    //     {
    //         if (reachability0(u, v))
    //         {
    //             my_dbg() << "reachability0(" << *graph[u] << ", " << *graph[v] << ")\n";
    //         }
    //     }
    // }
    // vector<InstState> states_ptr;
    vector<int> degrees(vertex_num, 0);
    // states_ptr.reserve(vertex_num * vertex_num * InstState::COUNT);
    // auto states = spanND(states_ptr.data(), vertex_num, InstState::COUNT, vertex_num);
    // auto states = unordered_map<InstState, vector<InstState>>();
    auto states = StatesMap(vertex_num);
    auto s1 = InstState(InstState::Zero);
    // states.states[s1].resize(vertex_num * vertex_num);
    // std::fill_n(states.states[s1].begin(), vertex_num * vertex_num, InstState(InstState::Unknown));
    graph.reachable(0ul, 0ul);
    dag_with_backedge.reachable(0ul, 0ul);
    for (auto u = 0u; u < vertex_num; ++u)
    {
        // my_dbg() << "calculate state for " << *graph[u] << "\n";
        // states_ptr.clear();
        unordered_set<int> search_space;
        vector<unsigned> zero_stack;
        for (auto e : to_range(boost::out_edges(u, dag_with_backedge.closure())))
        {
            auto v = boost::target(e, dag_with_backedge.closure());
            search_space.insert(v);
            for (auto e_in : to_range(boost::in_edges(v, dag_with_backedge.getGraph())))
            {
                auto w = boost::source(e_in, dag_with_backedge.getGraph());
                // if (reachability0(u, w) || u == w)
                if (dag_with_backedge.reachable(u, w))
                {
                    // my_dbg() << "N(" << *graph[u] << ", " << *graph[w] << "-> " << *graph[v] << "\n";
                    degrees[v]++;
                }
            }
        }

        // dump degrees
        // for (auto v : search_space)
        // {
        //     my_dbg() << "degree of " << *graph[v] << ": " << degrees[v] << "\n";
        // }

        zero_stack.push_back(u);
        states(u, InstState::Zero, u) = InstState(InstState::Zero);
        states.states[s1][u * vertex_num + u] = InstState(InstState::Zero);

        while (!zero_stack.empty())
        {
            auto target = zero_stack.back();
            zero_stack.pop_back();
            for (auto e : to_range(boost::out_edges(target, dag_with_backedge.getGraph())))
            {
                auto v = boost::target(e, dag_with_backedge.getGraph());
                degrees[v]--;
                if (degrees[v] == 0)
                {
                    zero_stack.push_back(v);
                }
            }
            if (u != target)
            {
                auto res =
                    statePropagation(u, InstState::Zero, states, target, dag_with_backedge, propagation_func_info);
                // if (res.isa(InstState::Substitute))
                // {
                //     res.substitution->zero_instr = graph[u];
                // }
                states(u, InstState::Zero, target) = res;
                // my_dbg() << "state propagation: " << *graph[u] << " -> " << *graph[target] << " = "
                //          << states(u, InstState::Zero, target).state << "\n";
            }
        }

        std::fill(degrees.begin(), degrees.end(), 0);
    }
    vector<vector<unsigned>> direct_dead_vertex(vertex_num);
    for (auto u = 0u; u < vertex_num; ++u)
    {
        for (auto v = 0u; v < vertex_num; ++v)
        {
            if (u != v && states(u, InstState::Zero, v).is_dead())
            {
                direct_dead_vertex[u].push_back(v);
            }
        }
    }
    // an approximation of indirect dead vertex
    // vector<vector<unsigned>> indirect_dead_vertex_star(vertex_num);
    // for (auto u = 0u; u < vertex_num; ++u)
    // {
    //     for (auto v : direct_dead_vertex[u])
    //     {
    //         for (auto w = 0u; w < vertex_num; ++w)
    //         {
    //             if (N(w, v) && !reachability0(w, u) && w != u)
    //             {
    //                 indirect_dead_vertex_star[u].push_back(w);
    //             }
    //         }
    //     }
    // }

    ValueGraph effective_graph;
    buildEffectiveGraph(graph, effective_graph);
    my_dbg() << "origin graph node num: " << boost::num_vertices(graph.getGraph()) << "\n";
    my_dbg() << "effective graph built\n";
    auto dom_info = DominanceInfo(effective_graph);
    my_dbg() << "effective graph node num: " << boost::num_vertices(dom_info.get_graph().getGraph()) << "\n";
    my_dbg() << "dom info built\n";
    std::vector<std::vector<unsigned>> indirect_dead_vertex(vertex_num);
    auto st = std::chrono::high_resolution_clock::now();
    partialDeadCodeSearch2(dom_info, states, direct_dead_vertex, graph, indirect_dead_vertex);
    auto ed = std::chrono::high_resolution_clock::now();
    fprintf(stderr,
            "[BACKWARD_SLICING] time: %ld\n",
            std::chrono::duration_cast<std::chrono::milliseconds>(ed - st).count());
    my_dbg() << "partial dead code search done\n";
    int __i = 0;
    for (auto direct : direct_dead_vertex)
    {
        my_dbg() << "direct dead vertex for node: " << __i++ << "\n";
        for (auto v : direct)
        {
            my_dbg() << "direct dead vertex: " << *graph[v] << "\n";
        }
    }

    __i = 0;
    for (auto indirect : indirect_dead_vertex)
    {
        my_dbg() << "indirect dead vertex for node: " << __i++ << "\n";
        for (auto v : indirect)
        {
            my_dbg() << "indirect dead vertex: " << *graph[v] << "\n";
        }
    }

    auto dead_vertex_star = indirect_dead_vertex;

    for (auto u = 0u; u < vertex_num; ++u)
    {
        // my_dbg() << "query dead vertex for " << *graph[u] << "\n";
        for (auto v : dead_vertex_star[u])
        {
            // my_dbg() << "dead vertex: " << *graph[v] << "\n";
        }
    }
    InstBenefitMap benefit_map;

    vector<int> benefits;

    for (auto u = 0u; u < vertex_num; ++u)
    {
        int benefit_u = 0;
        for (auto v : dead_vertex_star[u])
        {
            if (v == u)
            {
                continue;
            }
            auto u_inst = dyn_cast<Instruction>(graph[u]);
            if (auto inst = dyn_cast<Instruction>(graph[v]))
            {
                auto v_benefit =
                    TIRA->getInstructionCost(inst, TargetTransformInfo::TCK_Latency).getValue().value_or(0);
                // TIRA->getInstructionCost(inst, TargetTransformInfo::TCK_RecipThroughput).getValue().value_or(0);
                if (isa<LoadInst>(inst))
                {
                    v_benefit = 50;
                }
                else if (isa<StoreInst>(inst))
                {
                    // v_benefit = 1;
                }
                // else if (isa<CallInst>(inst))
                // {
                //     v_benefit = 200;
                // }
                if (v_benefit != 0)
                {
                    benefit_map[u].emplace(v, v_benefit);
                }
                if (auto v_loop = loop_info->getLoopFor(inst->getParent());
                    v_loop && (!u_inst || v_loop != loop_info->getLoopFor(u_inst->getParent())))
                {
                    // my_dbg() << "v in loop ant u not in: " << *inst << "\n";
                    v_benefit *= 10;
                }
                benefit_u += v_benefit;
                // my_dbg() << "benefit of " << *inst << ": " << v_benefit << "\n";
            }
        }
        benefits.push_back(benefit_u);
    }

    delete llvm::cast<UserOp1Inst>(effective_graph[0ul]);

    return ZeroBenefitAnalysisResult(std::move(graph),
                                     std::move(benefits),
                                     std::move(direct_dead_vertex),
                                     std::move(indirect_dead_vertex),
                                     std::move(benefit_map),
                                     std::move(states));
}
class AnalysisTestPass : public PassInfoMixin<AnalysisTestPass>
{
public:
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM)
    {
        LoopSimplifyPass().run(F, AM);
        LCSSAPass().run(F, AM);
        my_dbg() << "F:" << F;
        auto st = std::chrono::high_resolution_clock::now();
        auto res = ZeroBenefitAnalysis().run(F, AM);
        auto ed = std::chrono::high_resolution_clock::now();
        fprintf(stderr,
                "[ZeroBenefitAnalysis] time: %ld\n",
                std::chrono::duration_cast<std::chrono::milliseconds>(ed - st).count());
        my_dbg() << "report benefit\n";
        for (auto i = 0u; i < res.size(); ++i)
        {
            my_dbg() << *res.getValue(i) << " benefit: " << res[i] << "\n";
        }

        return PreservedAnalyses::all();
    }
};
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo()
{
    return {LLVM_PLUGIN_API_VERSION, "DetectZero", LLVM_VERSION_STRING, [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, llvm::FunctionPassManager &PM, ArrayRef<llvm::PassBuilder::PipelineElement>) {
                        if (Name == "--zero-benefit-analysis")
                        {
                            PM.addPass(AnalysisTestPass());
                            return true;
                        }
                        return false;
                    });
                PB.registerVectorizerStartEPCallback(
                    [](llvm::FunctionPassManager &FPM, llvm::OptimizationLevel O) { FPM.addPass(AnalysisTestPass()); });
                PB.registerAnalysisRegistrationCallback([](FunctionAnalysisManager &AM) {
                    AM.registerPass([&] { return TargetIRAnalysis(); });
                    AM.registerPass([&] { return LoopAnalysis(); });
                });
            }};
}