#include "ZeroSpecOpt.h"
#include "GraphBuilder.h"
#include "userop.h"
#include "utils.h"
#include "ZeroBenefitAnalysis.h"
#include "llvm/IR/Dominators.h"
#include <cstdio>
#include <fcntl.h>
#include <sys/file.h>
#include <fmt/format.h>
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/MDBuilder.h"
#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Analysis/DominanceFrontier.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constant.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/User.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include "llvm/Passes/PassPlugin.h"
#include <llvm/IR/PassManager.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/Debug.h>
#include <stdexcept>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <cstdlib>
#include <string>
#include <string_view>
#include <set>
#include "probe_helper.h"
#include <UnionFindSet.hpp>
#include <filesystem>
#include <developing.h>
#include "BlockCloneHelper.hpp"

// #define dbgs dummy_dbgs
namespace fs = std::filesystem;
using namespace std::string_literals;
using std::string_view;
using std::string;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::set;
using std::map;
using std::multiset;

bool has_optimize_target = false;
template <typename K, typename V>
class OrderedBimap
{
    set<std::pair<K, V>> values;
    std::map<K, decltype(values.begin())> _map;

public:
    void insert(K key, V value)
    {
        auto it = values.insert({key, value});
        _map[key] = it.first;
    }
    void erase(K key)
    {
        auto iter = _map[key];
        values.erase(iter);
        _map.erase(key);
    }
    V &at(K key) { return _map.at(key)->second; }
    decltype(values.begin()) begin() { return values.begin(); }
    decltype(values.end()) end() { return values.end(); }
    decltype(values.rbegin()) rbegin() { return values.rbegin(); }
    decltype(values.rend()) rend() { return values.rend(); }
    V &operator[](K key) { return _map[key]->second; }
    bool contains(K key) const { return _map.find(key) != _map.end(); }
    bool empty() const { return values.empty(); }
};

using namespace llvm;

static std::string getUniqueFuncName(VectorType *VecTy)
{
    std::string Name = "cmp_zero_vec_";
    raw_string_ostream RSO(Name);
    RSO << (VecTy->isScalableTy() ? "sve" : "fixed");
    RSO << "_" << VecTy->getElementType()->getTypeID();
    RSO << "_" << VecTy->getElementCount().getKnownMinValue();
    RSO << "_" << VecTy->getElementType()->getScalarSizeInBits();
    return RSO.str();
}

Function *getOrCreateVectorCmpFunc(Module &M, VectorType *VecTy)
{
    LLVMContext &Ctx = M.getContext();
    std::string Name = getUniqueFuncName(VecTy);

    if (Function *F = M.getFunction(Name))
    {
        return F;
    }

    Type *RetTy = Type::getInt1Ty(Ctx);
    Type *i32Ty = Type::getInt32Ty(Ctx);
    FunctionType *FuncTy = FunctionType::get(RetTy, {VecTy}, false);
    Function *F = Function::Create(FuncTy, Function::InternalLinkage, Name, &M);

    BasicBlock *BB = BasicBlock::Create(Ctx, "entry", F);
    IRBuilder<> B(BB);

    Argument *Arg = F->getArg(0);
    Value *Zero = Constant::getNullValue(VecTy);

    Value *Cmp = nullptr;
    if (VecTy->getElementType()->isFloatingPointTy())
    {
        Cmp = B.CreateFCmpOEQ(Arg, Zero, "fcmp");
    }
    else
    {
        Cmp = B.CreateICmpEQ(Arg, Zero, "icmp");
    }

    if (Cmp->getType()->isVectorTy())
    {
        Function *ReduceAnd = Intrinsic::getDeclaration(&M, Intrinsic::vector_reduce_and, {Cmp->getType()});
        Cmp = B.CreateCall(ReduceAnd, {Cmp}, "reduce");
    }

    B.CreateRet(Cmp);
    return F;
}
void dump_opt_targets(Function &F, const std::vector<std::tuple<long, long, long, long, long, double, double>> &info)
{
    auto allocate_buffer_call = search_allocate_buffer_call(F);
    // my_dbg() << "[ALLOCATE_BUFFER_CALL]" << *allocate_buffer_call << "\n";
    auto loc_name_val = cast<GlobalVariable>(allocate_buffer_call->getArgOperand(0));
    auto loc_name_ir = cast<ConstantDataArray>(loc_name_val->getInitializer());
    auto loc_name = loc_name_ir->getAsString().trim('\0');

    FILE *f = fopen(getenv("ZERO_SPEC_TARGETS_LOG"), "a");
    flock(fileno(f), LOCK_EX);
    for (auto [u, direct_count, dead_count, zero_count, total_count, zero_ratio, benefit] : info)
    {
        if (dead_count != 0)
        {
            fprintf(f,
                    "%s %ld %ld %ld %ld %ld %f %f\n",
                    loc_name.str().c_str(),
                    u,
                    direct_count,
                    dead_count,
                    zero_count,
                    total_count,
                    zero_ratio,
                    benefit);
        }
    }
    flock(fileno(f), LOCK_UN);
    fclose(f);
}

// instrumentation id -> (zero ratio, total issued count)
using zero_info_t = std::unordered_map<int, std::tuple<double, APInt, APInt>>;
zero_info_t load_zero_info(llvm::Function &F, const char *zero_info_path)
{
    auto allocate_buffer_call = search_allocate_buffer_call(F);
    if (!allocate_buffer_call)
    {
        my_dbg() << "no allocate buffer call for " << F.getName() << "\n";
        return {};
    }
    // my_dbg() << "[ALLOCATE_BUFFER_CALL]" << *allocate_buffer_call << "\n";
    auto loc_name_val = cast<GlobalVariable>(allocate_buffer_call->getArgOperand(0));
    auto loc_name_ir = cast<ConstantDataArray>(loc_name_val->getInitializer());
    auto loc_name = loc_name_ir->getAsString().trim('\0');
    my_dbg() << "[LOC_NAME]" << loc_name << "\n";

    zero_info_t zero_info;
    vector<std::string> zero_info_files;
    FILE *f = fopen(zero_info_path, "r");
    if (!f)
    {
        fprintf(stderr, "open zero info file failed\n");
        exit(-1);
    }
    char buffer[1024];
    while (true)
    {
        fgets(buffer, 1024, f);
        if (feof(f))
        {
            break;
        }
        auto line = llvm::StringRef(buffer);
        // my_dbg() << "[BUFFER]" << buffer << "\n";
        // for (int i = 0; i < loc_name.size(); ++i)
        // {
        //     if (line[i] != loc_name[i])
        //     {
        //         my_dbg() << "i: " << i << "," << (int)line[i] << "," << (int)loc_name[i] << "\n";
        //     }
        // }
        // if (!line.starts_with(loc_name))
        // {
        //     continue;
        // }
        SmallVector<StringRef> parts;
        line.split(parts, ' ');
        if (parts[0] != loc_name)
        {
            continue;
        }
        my_dbg() << "[PARTS] " << parts[1] << "\n";
        APInt id;
        parts[1].getAsInteger(10, id);
        double zero_ratio;
        parts[2].getAsDouble(zero_ratio);
        APInt total_count;
        if (zero_ratio < 0.1)
        {
            zero_ratio = 0;
        }
        parts[3].getAsInteger(10, total_count);
        if (total_count.getZExtValue() < 100)
        {
            zero_ratio = 0;
        }
        APInt predict_hit_count;
        parts[6].getAsInteger(10, predict_hit_count);
        zero_info[id.getZExtValue()] = {zero_ratio, total_count, predict_hit_count};
    }
    return zero_info;
}

auto build_benefit_map(const ZeroBenefitAnalysisResult &benefit_result)
{
    // benefit of v, u, v; u == 0 -> v is dead
    // set<std::tuple<int, int, int>> benefit_set;
    OrderedBimap<std::pair<int, int>, int> benefit_map;
    const auto &direct_dead_vertexs = benefit_result.direct_dead_vertex;
    const auto &inst_benefit_map = benefit_result.inst_benefit_map;
    for (const auto &[u, vs] : enumerate(direct_dead_vertexs))
    {
        for (auto v : vs)
        {
            auto iter1 = inst_benefit_map.find(u);
            if (iter1 == inst_benefit_map.end())
            {
                continue;
            }
            auto iter2 = iter1->second.find(v);
            if (iter2 == iter1->second.end())
            {
                continue;
            }
            my_dbg() << "insert u, v" << u << ", " << v << "\n";
            benefit_map.insert({u, v}, iter2->second);
        }
    }
    return benefit_map;
}

/**
 * @brief range of [begin, end)
 * 
 */
struct Interval
{
    int begin;
    int end;
    bool valid() const { return begin != -1 && end != -1 && begin < end; }
    bool overlap(Interval other) const { return other.begin < end && other.end > begin; }
    bool conj(Interval other) const { return this->end == other.begin || other.end == this->begin; }
    static Interval merge(Interval v1, Interval v2) { return {std::min(v1.begin, v2.begin), std::max(v1.end, v2.end)}; }
    bool operator<(Interval other) const { return this->begin < other.begin; }
    bool contains(int u) const { return u >= begin && u < end; }
};

class InstIntervalManager
{
    unordered_map<Instruction *, int> inst2id;
    vector<Instruction *> id2inst;
    // unordered_map<BasicBlock *, Interval> block2interval;
    set<int> block_borders;

    set<Interval> marked_interval;

public:
    InstIntervalManager(Function &F)
    {
        int id = 0;
        block_borders.insert(0);
        for (auto &bb : F)
        {
            // block2interval[&bb] = {id, id + (int)bb.size()};
            block_borders.insert(id + bb.size());
            for (auto &inst : bb)
            {
                inst2id[&inst] = id;
                id2inst.push_back(&inst);
                id++;
            }
        }
    }

    Interval get_unmarked_range(int u) const
    {
        auto block_upper_iter = block_borders.upper_bound(u);
        int block_end = *block_upper_iter;
        int block_begin = *(--block_upper_iter);
        if (marked_interval.empty())
        {
            return {block_begin, block_end};
        }
        auto interval_upper_iter = marked_interval.upper_bound({u, u});
        if (interval_upper_iter == marked_interval.begin())
        {
            return {block_begin, std::min(block_end, interval_upper_iter->begin)};
        }

        auto interval_lower_iter = interval_upper_iter;
        --interval_lower_iter;
        if (interval_lower_iter->contains(u))
        {
            return {-1, -1};
        }
        if (interval_upper_iter == marked_interval.end())
        {
            return {std::max(interval_lower_iter->end, block_begin), block_end};
        }

        return {std::max(block_begin, interval_lower_iter->end), std::min(block_end, interval_upper_iter->begin)};
    }

    bool mark_range(Interval i)
    {
        auto block_upper_iter = block_borders.upper_bound(i.begin);
        int block_end = *block_upper_iter;
        if (i.end > block_end)
        {
            return false;
        }
        Interval unmarked_range = get_unmarked_range(i.begin);
        // no unmarked range
        if (!unmarked_range.valid())
        {
            return false;
        }
        // i is not subset of unmarked range
        if (i.end > unmarked_range.end)
        {
            return false;
        }
        auto upper_iter = marked_interval.upper_bound(i);
        auto lower_iter = upper_iter;
        --lower_iter;
        Interval res = i;
        if (lower_iter->conj(res))
        {
            res.begin = lower_iter->begin;
            marked_interval.erase(lower_iter);
        }
        if (upper_iter->conj(res))
        {
            res.end = upper_iter->end;
            marked_interval.erase(upper_iter);
        }
        marked_interval.insert(res);
        return true;
    }

    bool has_marked_range(BasicBlock *bb)
    {
        auto block_begin = inst2id.at(&bb->front());
        auto block_end = inst2id.at(&bb->back()) + 1;
        auto unmarked_range = get_unmarked_range(block_begin);
        if (!unmarked_range.valid())
        {
            return true;
        }
        if (unmarked_range.begin != block_begin || unmarked_range.end != block_end)
        {
            return true;
        }
        return false;
    }

    Interval get_block_interval(BasicBlock *bb)
    {
        auto block_begin = inst2id.at(&bb->front());
        auto block_end = inst2id.at(&bb->back()) + 1;
        return {block_begin, block_end};
    }

    void mark_range(BasicBlock *bb)
    {
        auto block_begin = inst2id.at(&bb->front());
        auto block_end = inst2id.at(&bb->back()) + 1;
        mark_range({block_begin, block_end});
    }

    void mark_range(Loop *loop)
    {
        for (auto bb : loop->getBlocks())
        {
            mark_range(bb);
        }
    }

    bool has_marked_range(Loop *loop)
    {
        for (auto bb : loop->getBlocks())
        {
            if (has_marked_range(bb))
            {
                return true;
            }
        }
        return false;
    }

    int operator[](Instruction *inst) const { return inst2id.at(inst); }
    Instruction *operator[](int id) const { return id2inst.at(id); }
};

Instruction *build_opt_zone(const llvm::DominatorTree &dt,
                            const std::vector<Instruction *> &propagate_insts,
                            std::vector<BasicBlock *> &opt_zone,
                            const ValueGraph &block_graph,
                            const std::string &opt_zone_prefix,
                            UserOp1Inst *&userop1,
                            Value *&optimize_target)
{
    llvm::Instruction *zone_entry_inst = propagate_insts.front();
    // if (auto i = dyn_cast<Instruction>(optimize_target))
    // {
    //     zone_entry_inst = i->getNextNonDebugInstruction();
    // }
    // else
    // llvm::Instruction *zone_entry_inst = propagate_insts.front();
    my_dbg() << *zone_entry_inst->getParent()->getParent() << "\n";
    for (auto inst : propagate_insts)
    {
        my_dbg() << "propagate inst: " << *inst << "\n";
        zone_entry_inst = dt.findNearestCommonDominator(zone_entry_inst, inst);
    }
    if (std::find(propagate_insts.begin(), propagate_insts.end(), zone_entry_inst) != propagate_insts.end())
    {
        if (zone_entry_inst->getPrevNonDebugInstruction())
        {
            zone_entry_inst = zone_entry_inst->getPrevNonDebugInstruction();
        }
        else
        {
            // llvm::Function *do_nothing =
            //     llvm::Intrinsic::getDeclaration(zone_entry_inst->getModule(), llvm::Intrinsic::donothing);
            // auto donothing = CallInst::Create(do_nothing, {}, "", zone_entry_inst);
            // donothing->insertBefore(zone_entry_inst);
            // zone_entry_inst = donothing;
            userop1 = UserOp1Inst::Create(zone_entry_inst->getContext());
            userop1->insertBefore(zone_entry_inst);
            zone_entry_inst = userop1;
        }
    }
    if (zone_entry_inst->getParent()->getName().starts_with("opt_zone") &&
        !zone_entry_inst->getParent()->getName().starts_with(opt_zone_prefix))
    {
        return nullptr;
    }

    my_dbg() << "zone entry inst: " << *zone_entry_inst << "\n";
    SmallVector<BasicBlock *> desc;
    dt.getDescendants(zone_entry_inst->getParent(), desc);
    for (auto bb : desc)
    {
        if (bb == zone_entry_inst->getParent())
        {
            continue;
        }
        // my_dbg() << "desc: " << block_graph[(Value *)bb] << *bb << "\n";
        for (auto inst : propagate_insts)
        {
            if (block_graph.reachable(bb, inst->getParent()))
            {
                for (auto iter = bb->begin(); iter != bb->end(); ++iter)
                {
                    my_dbg() << "Inst in zone : " << *iter << "\n";
                }
                my_dbg() << "zone: " << *bb << "\n";
                if (bb->getName().starts_with("opt_zone") && !bb->getName().starts_with(opt_zone_prefix))
                {
                    opt_zone.clear();
                    return nullptr;
                }
                opt_zone.push_back(bb);
                break;
            }
        }
    }

    for (auto [i, bb] : llvm::enumerate(opt_zone))
    {
        bb->setName(opt_zone_prefix + std::to_string(i));
    }
    // for (int i = 0; i < block_graph.getGraph().m_vertices.size(); ++i)
    // {
    //     for (int j = 0; j < block_graph.getGraph().m_vertices.size(); ++j)
    //     {
    //         if (block_graph.get_reachability()(i, j))
    //         {
    //             my_dbg() << "reachable: " << i << ", " << j << "\n";
    //         }
    //     }
    // }
    return zone_entry_inst;
}

int search_best_opt_target(const std::vector<int> &benefit)
{
    int id = 0;
    for (unsigned int i = 0; i < benefit.size(); ++i)
    {
        if (benefit[i] > benefit[id])
        {
            id = i;
        }
    }
    return id;
}

struct log_type
{
    size_t instrumentation_id;
    size_t direct_count;
    size_t indirect_count;
    size_t zero_count;
    size_t total_count;
    double zero_ratio;
    double static_benefit;
    double dynamic_benefit;
    double sort_benefit;
};
void search_optimize_candidates(llvm::Function &F,
                                ZeroBenefitAnalysisResult &benefit_result,
                                const zero_info_t &zero_info,
                                vector<std::pair<int, log_type>> &optimize_candidates,
                                double delta, 
                                TargetTransformInfo* TIRA)
{
    unordered_map<int, int> zero_ratio_map;
    unordered_map<Value *, int> zero_count_map;
    vector<CallInst *> instrument_checks;
    unordered_map<Value *, double> weighted_benefits;
    unordered_map<Value *, int> instrumentation_id_map;
    search_instrumetation_check_calls(F, instrument_checks);
    int dbg_optimize_id = -1;
    if (getenv("DBG_OPTIMIZE_ID"))
    {
        dbg_optimize_id = std::stoi(getenv("DBG_OPTIMIZE_ID"));
        my_dbg() << "dbg optimize id: " << dbg_optimize_id << "\n";
    }
    auto log_path = getenv("ZERO_SPEC_TARGETS_LOG");
    std::vector<std::tuple<long, long, long, long, long, double, double>> log;
    size_t total_cost = 0;
    for (auto call : instrument_checks)
    {
        auto instrumentation_id = get_instrumeitation_id_in_func(call);
        auto iter = zero_info.find(instrumentation_id);
        if (iter == zero_info.end())
        {
            my_dbg() << "[WARNING]"
                     << "no zero info for " << *call << ": " << instrumentation_id << ": " << F.getName() << "\n";
            continue;
        }
        auto [zero_ratio, total_count, predict_hit_count] = iter->second;
        zero_ratio_map[benefit_result.graph[(get_instrumentation_target(call))]] = zero_ratio;
        zero_count_map[get_instrumentation_target(call)] = total_count.getZExtValue() * zero_ratio;
        if (auto inst = dyn_cast<Instruction>(get_instrumentation_target(call)))
        {
            if (isa<LoadInst>(inst))
            {

            total_cost += 50 * total_count.getZExtValue();
            }
            // else if (isa<CallInst>(inst))
            // {

            // total_cost += 200 * total_count.getZExtValue();
            // }
            else
            {
            total_cost += TIRA->getInstructionCost(inst, TargetTransformInfo::TCK_Latency).getValue().value_or(0) * total_count.getZExtValue();
            }
        }
    }

    // for (auto &bb : F)
    {
        // for (auto &instr : bb)
        {
            // if (is_instrument_check(&instr))
            for (auto instr : instrument_checks)
            {
                auto instrumentation_id = get_instrumeitation_id_in_func(cast<CallInst>(instr));
                if (dbg_optimize_id != -1)
                {
                    if (instrumentation_id != dbg_optimize_id)
                    {
                        continue;
                    }
                }
                my_dbg() << "instrumentation id: " << instrumentation_id << "\n";
                auto iter = zero_info.find(instrumentation_id);
                if (iter == zero_info.end())
                {
                    my_dbg() << "[WARNING]"
                             << "no zero info for " << instr << ": " << instrumentation_id << ": " << F.getName()
                             << "\n";
                    continue;
                }
                double weighted_benefit = 0;
                auto [zero_ratio, total_count, predict_hit_count] = iter->second;
                auto inst_id = benefit_result.graph[(get_instrumentation_target(instr))];
                auto instrumetation_target = get_instrumentation_target(instr);
                static int benefit_threshold = getenv("ZERO_BENEFIT_THRESHOLD") ? atoi(getenv("ZERO_BENEFIT_THRESHOLD")) : 0;
                if (benefit_result.benefit[inst_id] < benefit_threshold)
                {
                    continue;
                }
                if (zero_ratio < 0.4)
                {
                    continue;
                }
                // if (!instrumetation_target->getType()->isVectorTy())
                // {
                //     continue;
                // }
                my_dbg() << "instrumetation target: " << *instrumetation_target << "\n";
                for (auto direct_dead_id : benefit_result.direct_dead_vertex[inst_id])
                {
                    auto direct_dead = benefit_result.graph[direct_dead_id];
                    my_dbg() << "direct dead: " << *direct_dead << "\n";
                }
                uint64_t max_count = total_count.getZExtValue();
                for (auto [v, benefit] : benefit_result.inst_benefit_map[inst_id])
                {
                    auto v_inst = dyn_cast<Instruction>(benefit_result.graph[v]);
                    my_dbg() << "dead v: " << *v_inst << "\n";
                    if (v_inst)
                    {
                        if (benefit_result.inst_benefit_map[inst_id][benefit_result.graph[v_inst]] < 0)
                        {
                            my_dbg() << "negative benefit: "
                                     << benefit_result.inst_benefit_map[inst_id][benefit_result.graph[v_inst]] << "\n";
                        }
                        // if (zero_count_map.find(v_inst) == zero_count_map.end() || zero_count_map.at(v_inst) <= 0)
                        if (zero_count_map.find(v_inst) == zero_count_map.end())
                        {
                            weighted_benefit +=
                                (double)benefit_result.inst_benefit_map[inst_id][benefit_result.graph[v_inst]] *
                                total_count.getZExtValue();
                        }
                        else
                        {
                            weighted_benefit +=
                                (double)benefit_result.inst_benefit_map[inst_id][benefit_result.graph[v_inst]] *
                                zero_count_map.at(v_inst);
                            max_count = std::max(max_count, (uint64_t)zero_count_map.at(v_inst));
                        }
                    }
                    my_dbg() << "current benefit: " << weighted_benefit << "\n";
                }
                // for (auto user : instrumetation_target->users())
                // {
                //     my_dbg() << "user: " << *user << "\n";
                //     if (auto user_inst = dyn_cast<Instruction>(user))
                //     {
                //         if (benefit_result.inst_benefit_map[inst_id].find(benefit_result.graph[user_inst]) !=
                //             benefit_result.inst_benefit_map[inst_id].end())
                //         {
                //             my_dbg() << *user_inst << " "
                //                    << benefit_result.inst_benefit_map[inst_id].at(benefit_result.graph[user_inst])
                //                    << "\n";
                //             if (zero_count_map.find(user_inst) == zero_count_map.end())
                //             {
                //                 weighted_benefit +=
                //                     (double)benefit_result.inst_benefit_map[inst_id][benefit_result.graph[user_inst]] *
                //                     total_count.getSExtValue();
                //             }
                //             else
                //             {
                //                 weighted_benefit +=
                //                     (double)benefit_result.inst_benefit_map[inst_id][benefit_result.graph[user_inst]] *
                //                     zero_count_map.at(user);
                //             }
                //         }
                //     }
                // }
                // if (zero_ratio == 0)
                // {
                //     weighted_benefit = 0;
                // }
                weighted_benefit /= total_count.getZExtValue();
                // my_dbg() << weighted_benefit << "\n";
                weighted_benefit *= zero_ratio;
                // my_dbg() << weighted_benefit << "\n";
                int branch_miss_cost = 9;
                if (getenv("ZERO_SPEC_BRANCH_MISS_COST"))
                {
                    branch_miss_cost = std::stoi(getenv("ZERO_SPEC_BRANCH_MISS_COST"));
                }
                weighted_benefit -=
                    (branch_miss_cost * (1 - (double)predict_hit_count.getZExtValue() / total_count.getZExtValue()));
                // my_dbg() << weighted_benefit << " " << branch_miss_cost << " " << predict_hit_count.getZExtValue() << " " << total_count.getZExtValue() << "\n";

                if (log_path)
                {
                    log.push_back({instrumentation_id,
                                   benefit_result.direct_dead_vertex[inst_id].size(),
                                   benefit_result.indirect_dead_vertex[inst_id].size(),
                                   (long)(zero_ratio * total_count.getZExtValue()),
                                   total_count.getZExtValue(),
                                   zero_ratio,
                                   weighted_benefit});
                }
                weighted_benefits[instrumetation_target] = weighted_benefit * max_count;
                instrumentation_id_map[instrumetation_target] = instrumentation_id;
                my_dbg() << "zero ratio: " << zero_ratio << "\n";
                my_dbg() << "benefit: " << weighted_benefit << "\n";
                if (weighted_benefit >= delta)
                {
                    my_dbg() << "optimize candidate: " << *instr << "\n";
                    optimize_candidates.push_back({(int)inst_id,
                                                   {(size_t)instrumentation_id,
                                                    benefit_result.direct_dead_vertex[inst_id].size(),
                                                    benefit_result.indirect_dead_vertex[inst_id].size(),
                                                    (size_t)(zero_ratio * total_count.getZExtValue()),
                                                    total_count.getZExtValue(),
                                                    zero_ratio,
                                                    (double)benefit_result.benefit[inst_id],
                                                    weighted_benefit,
                                                    weighted_benefits[instrumetation_target]}});
                }
                else
                {
                    my_dbg() << "not optimize candidate: " << *instr << "|" << zero_ratio << "|"
                             << benefit_result[inst_id] << "|" << delta << "\n";
                }
            }
        }
    }
    // if (log_path)
    // {
    //     dump_opt_targets(F, log);
    // }
    std::sort(
        optimize_candidates.begin(),
        optimize_candidates.end(),
        [&benefit_result, &weighted_benefits](const std::pair<int, log_type> &a, const std::pair<int, log_type> &b) {
            return weighted_benefits.at(benefit_result.graph[a.first]) >
                   weighted_benefits.at(benefit_result.graph[b.first]);
        });
    if (!optimize_candidates.empty())
    {
        my_dbg() << "function name: " << F.getName() << "\n";
        for (auto [i, id_group] : enumerate(optimize_candidates))
        {
            auto id = id_group.first;
            my_dbg() << "optimize candidate[" << i << "]: " << instrumentation_id_map.at(benefit_result.graph[id])
                     << "\n";
        }
        // my_dbg() << "optimize candidate[0]: " << instrumentation_id_map.at(benefit_result.graph[optimize_candidates[0]])
        //          << "\n";
    }
    fprintf(stderr, "[TOTAL COST] %ld\n", total_cost);
}

void propagate_optimize(BlocksCloneHelper &clone_helper, int optimize_target, ZeroBenefitAnalysisResult &benefit_result)
{
    auto &inst_graph = benefit_result.graph;
    for (auto w : benefit_result.direct_dead_vertex[optimize_target])
    {
        auto w_inst = dyn_cast<Instruction>(inst_graph[w]);
        my_dbg() << "optimize w: " << *w_inst << "\n";
        if (w_inst && clone_helper.contains(w_inst))
        {
            auto w_state = benefit_result.states(optimize_target, InstState::Zero, w);
            my_dbg() << "w state: " << w_state.state << "\n";
            auto cloned_w_val = clone_helper[w_inst];
            // TODO: add other state propagation
            if (w_state.isa(InstState::Zero))
            {
                if (w_inst->getType()->isIntegerTy())
                {
                    cloned_w_val->replaceAllUsesWith(llvm::ConstantInt::get(w_inst->getType(), 0));
                }
                else if (w_inst->getType()->isFloatingPointTy())
                {
                    cloned_w_val->replaceAllUsesWith(llvm::ConstantFP::get(w_inst->getType(), 0));
                }
                else if (isa<StoreInst>(w_inst))
                {
                }
                else if (w_inst->getType()->isVectorTy() && w_inst->getType()->isIntOrIntVectorTy())
                {
                    auto vec_ty = cast<VectorType>(w_inst->getType());
                    auto zero_vec = llvm::ConstantVector::getSplat(vec_ty->getElementCount(),
                                                                   llvm::ConstantInt::get(vec_ty->getElementType(), 0));
                    cloned_w_val->replaceAllUsesWith(zero_vec);
                }
                else if (w_inst->getType()->isVectorTy() && w_inst->getType()->isFPOrFPVectorTy())
                {
                    auto vec_ty = cast<VectorType>(w_inst->getType());
                    auto zero_vec = llvm::ConstantVector::getSplat(vec_ty->getElementCount(),
                                                                   llvm::ConstantFP::get(vec_ty->getElementType(), 0));
                    cloned_w_val->replaceAllUsesWith(zero_vec);
                }
                else
                {
                    // TODO: fix other type
                    my_dbg() << "unhandled inst: " << *w_inst << "\n";
                    my_dbg() << "unhandled type: " << *w_inst->getType() << "\n";
                    throw std::runtime_error("unhandled type");
                }
                if (auto cloned_instr = dyn_cast<Instruction>(cloned_w_val))
                {
                    cloned_instr->eraseFromParent();
                }
            }
            else if (w_state.isa(InstState::Substitute))
            {
                // auto w_val = w.get<Value *>();
                auto w_val = w_state.get_value(inst_graph, w);
                if (auto i = dyn_cast<Instruction>(w_val))
                {
                    my_dbg() << "clone_helper[w_inst] " << *cloned_w_val << "\n";
                    if (clone_helper.contains(i))
                    {
                        my_dbg() << "i: " << *i << "\n";
                        my_dbg() << "replace with: " << *clone_helper[i] << "\n";
                        cloned_w_val->replaceAllUsesWith(clone_helper[i]);
                    }
                    else
                    {
                        my_dbg() << "replace with-: " << *i << "\n";
                        cloned_w_val->replaceAllUsesWith(i);
                    }
                    if (auto cloned_instr = dyn_cast<Instruction>(cloned_w_val))
                    {
                        cloned_instr->eraseFromParent();
                    }
                }
                else
                {
                    my_dbg() << "clone_helper[w_inst] " << *cloned_w_val << "\n";
                    my_dbg() << "replace with: " << *w_val << "\n";
                    cloned_w_val->replaceAllUsesWith(w_val);
                    if (auto cloned_instr = dyn_cast<Instruction>(cloned_w_val))
                    {
                        cloned_instr->eraseFromParent();
                    }
                }
            }
            else if (w_state.isa(InstState::Constant))
            {
                if (w_state.is_float)
                {
                    cloned_w_val->replaceAllUsesWith(llvm::ConstantFP::get(w_inst->getType(), w_state.get<double>()));
                }
                else
                {
                    my_dbg() << "clone_helper[w_inst] " << *cloned_w_val << "\n";
                    my_dbg() << "replace with: " << w_state.get<long>() << "\n";
                    cloned_w_val->replaceAllUsesWith(llvm::ConstantInt::get(w_inst->getType(), w_state.get<long>()));
                }
                if (auto cloned_instr = dyn_cast<Instruction>(cloned_w_val))
                {
                    cloned_instr->eraseFromParent();
                }
            }
        }
    }
}

void sink_optimize(BasicBlock *zero_header,
                   ZeroBenefitAnalysisResult &result,
                   Value *optimize_target,
                   const std::string &opt_zone_prefix)
{
    my_dbg() << "sink optimize\n";
    auto &inst_graph = result.graph;
    auto &indirect_dead_vertex = result.indirect_dead_vertex;
    ValueGraph dead_graph;
    std::set<unsigned> indirects;
    for (auto u : indirect_dead_vertex[inst_graph[optimize_target]])
    {
        if (auto inst = dyn_cast<Instruction>(inst_graph[u]))
        {
            // if (!inst->getParent()->getName().starts_with(opt_zone_prefix))
            if (!inst->getParent()->getName().starts_with(opt_zone_prefix) ||
                inst->getParent()->getName().ends_with("entry"))
            {
                indirects.insert(u);
            }
        }
    }
    for (auto direct : result.direct_dead_vertex[inst_graph[optimize_target]])
    {
        indirects.erase(direct);
    }
    for (auto value : indirects)
    {
        if (isa<Instruction>(inst_graph[value]))
        {
            dead_graph.addVertex(inst_graph[value]);
            my_dbg() << "add vertex: " << *inst_graph[value] << "\n";
        }
    }
    for (auto value : indirects)
    {
        auto value_inst = dyn_cast<Instruction>(inst_graph[value]);
        for (auto &op : cast<Instruction>(inst_graph[value])->operands())
        {
            if (auto op_inst = dyn_cast<Instruction>(op.get()))
            {
                if (op_inst == value_inst)
                {
                    continue;
                }
                if (dead_graph.contains(op_inst))
                {
                    dead_graph.addEdge(op_inst, inst_graph[value]);
                    my_dbg() << "add edge: " << *op_inst << " -> " << *value_inst << "\n";
                }
            }
        }
    }

    my_dbg() << "zero header: " << *zero_header << "\n";
    auto topo = dead_graph.build_topo();
    for (auto vid : (topo))
    {
        auto v = dead_graph[vid];
        my_dbg() << "sink v: " << *v << "\n";
        if (auto v_inst = dyn_cast<Instruction>(v))
        {
            if (v_inst->getParent() != zero_header)
            {
                v_inst->moveBefore(&*zero_header->getFirstInsertionPt());
                for (auto user : v_inst->users())
                {
                    if (isa<UserOp2Inst>(user))
                    {
                        continue;
                    }
                    if (is_instrument_check(user))
                    {
                        cast<Instruction>(user)->moveAfter(v_inst);
                    }
                }
            }
        }
    }
}

// void dump_opt_target(long u, long deac_count, long zero_ratio)
void dump_opt_targets(llvm::Function &F, const ZeroBenefitAnalysisResult &result, zero_info_t &zero_info)
{
    auto &dead_set = result.indirect_dead_vertex;
    FILE *f = fopen(getenv("ZERO_SPEC_TARGETS_LOG"), "a");
    flock(fileno(f), LOCK_EX);
    for (auto [u, vs] : llvm::enumerate(dead_set))
    {
        double zero_ratio = -1;
        int instrumentation_id = -1;
        for (auto user : result.graph[u]->users())
        {
            if (auto call = dyn_cast<CallInst>(user); is_instrument_check(call))
            {
                instrumentation_id = get_instrumeitation_id_in_func(call);
                auto iter = zero_info.find(instrumentation_id);
                if (iter != zero_info.end())
                {
                    zero_ratio = std::get<0>(iter->second);
                    break;
                }
            }
        }
        if (vs.size() != 0)
        {
            fprintf(f, "%s %d %ld %lf\n", F.getName().str().c_str(), instrumentation_id, vs.size(), zero_ratio);
        }
    }
    flock(fileno(f), LOCK_UN);
    fclose(f);
}

llvm::PreservedAnalyses ZeroSpecOpt::_run(llvm::Function &F, llvm::FunctionAnalysisManager &FAM)
{
    my_dbg() << "enter pass for " << F.getName() << "\n";
    if (!F.hasFnAttribute("zero-instrumented"))
    {
        return llvm::PreservedAnalyses::all();
    }
    if (getenv("DETECT_TARGET_FUNC") && F.getName() != getenv("DETECT_TARGET_FUNC"))
    {
        return llvm::PreservedAnalyses::all();
    }
    auto zero_info_path = getenv("ZERO_SPEC_DB");
    if (!zero_info_path)
    {
        fprintf(stderr, "ZERO_SPEC_DB not set\n");
        exit(-1);
    }

    auto *TIRA = &FAM.getResult<TargetIRAnalysis>(F);
    auto zero_info = load_zero_info(F, zero_info_path);
    if (zero_info.empty())
    {
        my_dbg() << "zero info empty\n";
        return llvm::PreservedAnalyses::all();
    }
    MDBuilder MDB(F.getContext());
    my_dbg() << "load zero info finish\n";
    auto instrument_checks = std::vector<CallInst *>();
    search_instrumetation_check_calls(F, instrument_checks);
    auto benefit_result = ZeroBenefitAnalysis().run(F, FAM);
    auto &dt = FAM.getResult<DominatorTreeAnalysis>(F);
    auto &df = FAM.getResult<DominanceFrontierAnalysis>(F);
    // auto &loop_info = FAM.getResult<LoopAnalysis>(F);
    auto &inst_graph = benefit_result.graph;
    // benefit of v, u, v where u == 0 -> v is dead.
    auto benefit_map = build_benefit_map(benefit_result);
    int delta = 8;
    if (getenv("ZERO_SPEC_OPT_DELTA"))
    {
        delta = std::stoi(getenv("ZERO_SPEC_OPT_DELTA"));
    }
    if (getenv("ZERO_SPEC_TARGETS_LOG"))
    {
        // dump_opt_targets(F, benefit_result, zero_info);
    }

    my_dbg() << "origin function: " << F << "\n";
    DominatorTree dom_tree(F);
    // unordered_map<int, map<std::pair<int, int>, std::pair<Instruction *, Instruction *>>> optimize_targets;
    vector<std::pair<int, vector<Interval>>> optimize_targets;
    vector<std::pair<int, log_type>> optimize_candidates;
    search_optimize_candidates(F, benefit_result, zero_info, optimize_candidates, delta, TIRA);
    if (!optimize_candidates.empty())
    {
        my_dbg() << "optimize candidates: ";
        for (auto id_group : optimize_candidates)
        {
            auto [id, _] = id_group;
            my_dbg() << *inst_graph[id] << ", ";
        }
        my_dbg() << "\n";
    }
    else
    {
        my_dbg() << "no optimize candidates for " << F.getName() << "\n";
        return llvm::PreservedAnalyses::none();
    }
    int blocks_num = 0;
    for (auto &bb : F)
    {
        blocks_num++;
    }
    int optimized_targets_num = 0;
    unsigned int MAX_OPTIMIZE_TARGETS = -1;
    if (getenv("MAX_OPTIMIZE_TARGETS"))
    {
        MAX_OPTIMIZE_TARGETS = std::stoi(getenv("MAX_OPTIMIZE_TARGETS"));
    }
    bool do_log = getenv("ZERO_SPEC_TARGETS_LOG");
    std::string opt_log = "";
    UnionFindSet ufs(blocks_num);
    for (auto [opt_zone_idx, optimize_target_group] : llvm::enumerate(optimize_candidates))
    {
        auto optimize_target = optimize_target_group.first;
        auto opt_zone_prefix = "opt_zone"s + std::to_string(opt_zone_idx) + "_";
        vector<BasicBlock *> opt_zone;
        vector<Instruction *> propagate_insts;
        auto optimize_target_value = inst_graph[optimize_target];
        Instruction *optimize_target_inst = dyn_cast<Instruction>(optimize_target_value);
        // only optimize the first candidate
        // for (auto &[v, benefit] : benefit_result.inst_benefit_map[optimize_target])
        for (auto v : benefit_result.direct_dead_vertex[optimize_target])
        {
            auto v_inst = dyn_cast<Instruction>(inst_graph[v]);
            propagate_insts.push_back(v_inst);
        }
        if (propagate_insts.empty())
        {
            continue;
        }
        auto &benefit_map_for_target = benefit_result.inst_benefit_map[optimize_target];
        // TODO: currently assume all propagate insts are optimized
        // if optimize_target_inst is a invoke, it mey be the last inst in the block
        if (optimize_target_inst && optimize_target_inst != &*optimize_target_inst->getParent()->rbegin())
        {
            if (optimize_target_inst->getParent()->getName().starts_with("opt_zone"))
            {
                continue;
            }
            my_dbg() << "optimize target inst: " << *optimize_target_inst << "\n";
            my_dbg() << "block for optimize target: " << *optimize_target_inst->getParent() << "\n";
            for (auto inst = optimize_target_inst->getNextNonDebugInstruction();
                 !inst->isTerminator() && (inst != &*inst->getParent()->rbegin());
                 inst = inst->getNextNonDebugInstruction())
            {
                if (benefit_map_for_target.find(inst_graph[(Value *)&inst]) != benefit_map_for_target.end())
                {
                    optimize_target_inst->getParent()->splitBasicBlock(
                        inst, opt_zone_prefix + "_entry_split_from_optimize_target");
                    break;
                }
            }
        }
        dt.recalculate(F);
        df.analyze(dt);

        // my_dbg() << "optimize target inst: " << *optimize_target_inst << "\n";

        auto block_graph = ValueGraph();
        build_basicblock_graph(F, block_graph);
        UserOp1Inst *userop1 = nullptr;
        auto zero_entry =
            build_opt_zone(dt, propagate_insts, opt_zone, block_graph, opt_zone_prefix, userop1, optimize_target_value);
        if (zero_entry == nullptr)
        {
            if (userop1)
            {
                userop1->eraseFromParent();
            }
            continue;
        }
        has_optimize_target = true;
        my_dbg() << "optimize target: " << *optimize_target_value << "\n";
        my_dbg() << "zero entry block: " << *zero_entry->getParent() << "\n";
        BasicBlock *opt_zone_header = nullptr;
        if (zero_entry->isTerminator())
        {
            if (zero_entry->getPrevNonDebugInstruction() == nullptr)
            {
                BasicBlock *new_bb = BasicBlock::Create(F.getContext(), "", &F);
                zero_entry->getParent()->replaceUsesWithIf(
                    new_bb, [](Use &U) { return isa<BranchInst, InvokeInst>(U.getUser()); });
                opt_zone_header = zero_entry->getParent();
                opt_zone_header->setName(opt_zone_prefix + "_header");
                BranchInst::Create(zero_entry->getParent(), new_bb);
                zero_entry = new_bb->getTerminator();
            }
            else
            {
                zero_entry = zero_entry->getPrevNonDebugInstruction();
                opt_zone_header = zero_entry->getParent()->splitBasicBlock(zero_entry->getNextNonDebugInstruction(),
                                                                           opt_zone_prefix + "_header");
            }
        }
        else
        {
            opt_zone_header = zero_entry->getParent()->splitBasicBlock(zero_entry->getNextNonDebugInstruction(),
                                                                       opt_zone_prefix + "_header");
        }
        opt_zone.push_back(opt_zone_header);
        zero_entry->getParent()->setName(opt_zone_prefix + "_entry");
        my_dbg() << "zero entry: " << zero_entry->getParent()->getName() << "\n";
        // auto opt_zone_header =
        //     zero_entry->getParent()->splitBasicBlock(zero_entry->getNextNonDebugInstruction(), "zero_header");
        // auto opt_zone_header = zero_entry->getParent();
        // opt_zone.push_back(opt_zone_header);
        block_graph = ValueGraph();
        dt.recalculate(F);
        df.analyze(dt);
        build_basicblock_graph(F, block_graph);
        auto clone_helper =
            BlocksCloneHelper(opt_zone_header, opt_zone, optimize_target_value, block_graph, dt, df, opt_zone_prefix);
        my_dbg() << "zero entry: " << *zero_entry << "\n";
        // zero_entry->getParent()->getTerminator()->eraseFromParent();
        auto zero_entry_term = zero_entry->getParent()->getTerminator();
        Instruction *zero_judge = nullptr;
        if (!optimize_target_value->getType()->isVectorTy())
        {
            zero_judge = optimize_target_value->getType()->isIntegerTy()
                             ? CmpInst::Create(Instruction::ICmp,
                                               CmpInst::ICMP_EQ,
                                               optimize_target_value,
                                               ConstantInt::get(optimize_target_value->getType(), 0),
                                               "zero_judge",
                                               zero_entry->getParent())
                             : CmpInst::Create(Instruction::FCmp,
                                               CmpInst::FCMP_OEQ,
                                               optimize_target_value,
                                               ConstantFP::get(optimize_target_value->getType(), 0),
                                               "zero_judge",
                                               zero_entry->getParent());
        }
        else
        {
            auto check_func =
                getOrCreateVectorCmpFunc(*F.getParent(), llvm::cast<VectorType>(optimize_target_value->getType()));
            zero_judge = CallInst::Create(check_func, {optimize_target_value}, "zero_judge", zero_entry->getParent());
        }
        auto br =
            BranchInst::Create(clone_helper[opt_zone_header], opt_zone_header, zero_judge, zero_entry->getParent());
        // MDNode *Weights = MDB.createBranchWeights(99, 1);
        // br->setMetadata(LLVMContext::MD_prof, Weights);
        zero_entry_term->eraseFromParent();
        my_dbg() << "Function before optimize: " << F << "\n";
        propagate_optimize(clone_helper, optimize_target, benefit_result);
        my_dbg() << "Function before sink: " << F << "\n";

        sink_optimize(opt_zone_header, benefit_result, optimize_target_value, opt_zone_prefix);

        my_dbg() << "Function: " << F << "\n";
        auto loop_info = LoopAnalysis().run(F, FAM);
        auto loop_depth = loop_info.getLoopDepth(zero_judge->getParent());
        auto loop = loop_info.getLoopFor(zero_judge->getParent());
        my_dbg() << "loop depth: " << loop_depth << "\n";
        my_dbg() << "loop: " << loop << "\n";
        // if (zero_entry_term != zero_entry && isa<UserOp1Inst>(zero_entry))
        // {
        //     zero_entry->eraseFromParent();
        // }
        if (userop1)
        {
            userop1->eraseFromParent();
        }
        if (do_log)
        {
            char buffer[256];
            snprintf(buffer,
                     sizeof(buffer),
                     "%s %lu %lu %lu %lu %lu %lf %lf %lf %lf\n",
                     F.getName().str().c_str(),
                     optimize_target_group.second.instrumentation_id,
                     optimize_target_group.second.direct_count,
                     optimize_target_group.second.indirect_count,
                     optimize_target_group.second.zero_count,
                     optimize_target_group.second.total_count,
                     optimize_target_group.second.zero_ratio,
                     optimize_target_group.second.static_benefit,
                     optimize_target_group.second.dynamic_benefit,
                     optimize_target_group.second.sort_benefit);
            opt_log += buffer;
        }

        optimized_targets_num++;
        if (optimized_targets_num >= MAX_OPTIMIZE_TARGETS)
        {
            break;
        }
    }
    if (do_log)
    {
        FILE *f = fopen(getenv("ZERO_SPEC_TARGETS_LOG"), "a");
        flock(fileno(f), LOCK_EX);
        fprintf(f, "[BEGIN]\n");
        fprintf(f, "%s", opt_log.c_str());
        fprintf(f, "[END]\n");
        flock(fileno(f), LOCK_UN);
        fclose(f);
    }

    verifyFunction(F, my_dbg());

    return llvm::PreservedAnalyses::none();
}
llvm::PreservedAnalyses ZeroSpecOpt::run(llvm::Function &F, llvm::FunctionAnalysisManager &FAM)
{
    // UserOp2Inst::Release();
    auto res = _run(F, FAM);
    if (has_optimize_target)
    {
        fprintf(stderr, "[INFO] has optimize target\n");
    }
    remove_instrumentations(F);
    ADCEPass().run(F, FAM);
    // UserOp2Inst::Release();
    return res;
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo()
{
    return {LLVM_PLUGIN_API_VERSION, "ZeroSpecOpt", LLVM_VERSION_STRING, [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, llvm::FunctionPassManager &PM, ArrayRef<llvm::PassBuilder::PipelineElement>) {
                        if (Name == "zero-spec-opt")
                        {
                            PM.addPass(ZeroSpecOpt());
                            return true;
                        }
                        return false;
                    });
                PB.registerVectorizerStartEPCallback(
                    [](llvm::FunctionPassManager &FPM, llvm::OptimizationLevel O) { FPM.addPass(ZeroSpecOpt()); });
                PB.registerAnalysisRegistrationCallback([](FunctionAnalysisManager &AM) {
                    AM.registerPass([&] { return ZeroBenefitAnalysis(); });
                    AM.registerPass([&] { return LoopAnalysis(); });
                    AM.registerPass([&] { return DominatorTreeAnalysis(); });
                    AM.registerPass([&] { return DominanceFrontierAnalysis(); });
                });
            }};
}