#include "probe_helper.h"
#include "probe.h"
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/Debug.h>
using namespace llvm;
bool is_instrument(const llvm::Value *v)
{
    auto call = dyn_cast<CallInst>(v);
    if (!call)
    {
        return false;
    }
    if (!call->getCalledFunction())
    {
        return false;
    }
    if (call->getCalledFunction()->getName().contains(INSTRUMENTATION_PREFIX_STR))
    {
        return true;
    }
    return false;
}
bool is_instrument_check(const llvm::Value *v)
{
    auto call = dyn_cast<CallInst>(v);
    if (!call)
    {
        return false;
    }
    if (!call->getCalledFunction())
    {
        return false;
    }
    if (call->getCalledFunction()->getName().contains(INSTRUMENTATION_PREFIX_STR) &&
        call->getCalledFunction()->getName().contains(CHECK_ZERO_PREFIX))
    {
        return true;
    }
    return false;
}
llvm::CallInst *search_allocate_buffer_call(llvm::Function &F)
{
    for (auto &bb : F)
    {
        for (auto &instr : bb)
        {
            if (auto call = llvm::dyn_cast<llvm::CallInst>(&instr))
            {
                auto callee = call->getCalledFunction();
                if (callee && callee->getFunction().getName() == INSTRUMENTATION_PREFIX_STR ALLOCATE_BUFFER_PREFIX)
                {
                    return call;
                }
            }
        }
    }
    return nullptr;
}
void search_instrumetation_check_calls(llvm::Function &F, std::vector<llvm::CallInst *> &instrument_checks)
{
    for (auto &bb : F)
    {
        for (auto &instr : bb)
        {
            if (auto call = llvm::dyn_cast<llvm::CallInst>(&instr))
            {
                if (!is_instrument_check(call))
                {
                    continue;
                }
                instrument_checks.push_back(call);
            }
        }
    }
}

int get_instrumeitation_id_in_func(llvm::CallInst *call)
{
    // my_dbg() << "call: " << *call << "\n";
    return cast<llvm::ConstantInt>(call->getArgOperand(2))->getSExtValue();
}
llvm::Value *get_instrumentation_target(llvm::Value *call) { return dyn_cast<CallInst>(call)->getOperand(0); }

void remove_instrumentations(llvm::Function &F)
{
    std::vector<Instruction *> delete_candidates;
    for (auto &bb : F)
    {
        for (auto &instr : bb)
        {
            if (auto call = dyn_cast<CallInst>(&instr))
            {
                if (is_instrument(call))
                {
                    delete_candidates.push_back(call);
                }
            }
        }
    }
    for (auto instr : delete_candidates)
    {
        instr->eraseFromParent();
    }
}