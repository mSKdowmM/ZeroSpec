#pragma once

#include "llvm/IR/PassManager.h"
#include <cassert>
#include "GraphBuilder.h"
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Use.h>
#include <llvm/IR/Value.h>
#include <vector>
#include <unordered_map>
#include <queue>
#include "userop.h"

struct InstBenefitMap
{
public:
    struct InstBenefit : std::pair<int, int>
    {
        InstBenefit(int id, int benefit)
        : std::pair<int, int>(id, benefit)
        {
        }
        int &id() { return first; };
        int &benefit() { return second; };
    };

private:
    // std::unordered_map<int, std::priority_queue<InstBenefit>> inst_map;
    std::unordered_map<int, std::unordered_map<int, int>> inst_map;

public:
    auto &operator[](int id) { return inst_map[id]; }
    const auto &at(int id) const { return inst_map.at(id); }
    auto find(int id) const { return inst_map.find(id); }
    auto begin() const { return inst_map.begin(); }
    auto end() const { return inst_map.end(); }
};
struct InstState
{
    enum State
    {
        Unknown = 0,
        Zero,
        Constant,
        Substitute,
        TOTAL_COUNT
    };
    constexpr static size_t COUNT = TOTAL_COUNT;
    union StateValue
    {
        long constant;
        double constant_fp;
    };
    // std::shared_ptr<llvm::UserOp2Inst> substitution;
    int substitution = -1;
    State state = Unknown;
    StateValue value{0};
    bool is_float = false;

    bool is_dead() const { return state == Zero || state == Constant || state == Substitute; }

    InstState() = default;
    InstState(long constant)
    : state(Constant)
    {
        value.constant = constant;
    }

    InstState(double constant)
    : state(Constant)
    {
        value.constant_fp = constant;
        is_float = true;
    }
    // InstState(llvm::Value *_substitution)
    // : state(Substitute)
    // {
    //     // substitution = std::make_shared<llvm::UserOp2Inst>(std::move(*llvm::UserOp2Inst::Create(_substitution)));
    //     // auto res = llvm::UserOp2Inst::Create(_substitution, llvm::UserOp2Inst::State);
    //     // substitution.reset(res);
    // }
    InstState(State _state)
    : state(_state)
    {
        assert(state != Constant && state != Substitute);
    }

    InstState &operator=(int constant)
    {
        state = Constant;
        value.constant = constant;
        return *this;
    }
    InstState &operator=(double constant)
    {
        state = Constant;
        value.constant_fp = constant;
        is_float = true;
        return *this;
    }

    // InstState &operator=(llvm::Value *_substitution)
    // {
    //     state = Substitute;
    //     // substitution = std::make_shared<llvm::UserOp2Inst>(std::move(*llvm::UserOp2Inst::Create(_substitution)));
    //     // substitution = std::make_shared<llvm::UserOp2Inst>(std::move(*llvm::UserOp2Inst::Create(_substitution)));
    //     substitution.reset(llvm::UserOp2Inst::Create(_substitution, llvm::UserOp2Inst::State));
    //     return *this;
    // }

    InstState &operator=(State _state)
    {
        assert(state != Constant && state != Substitute);
        this->state = _state;
        return *this;
    }

    InstState &operator=(const InstState &other)
    {
        state = other.state;
        value = other.value;
        is_float = other.is_float;
        this->substitution = other.substitution;
        return *this;
    }

    InstState(const InstState &other)
    {
        state = other.state;
        value = other.value;
        is_float = other.is_float;
        this->substitution = other.substitution;
    }

    static InstState get_substitute(int substitution)
    {
        InstState res;
        res.state = Substitute;
        res.substitution = substitution;
        return res;
    }

    bool operator==(const InstState &other) const
    {
        return state == other.state && value.constant == other.value.constant && substitution == other.substitution &&
               is_float == other.is_float;
    }

    bool operator!=(const InstState &other) const { return !(*this == other); }

    bool isa(State _state) const { return this->state == _state; }

    llvm::Value *get_value(const ValueGraph &graph, llvm::Value *v) const
    {
        if (!llvm::isa<llvm::Instruction>(v))
        {
            return nullptr;
        }
        if (isa(InstState::Substitute))
        {
            return llvm::cast<llvm::Instruction>(v)->getOperand(substitution);
        }
        return nullptr;
    }
    llvm::Value *get_value(const ValueGraph &graph, int v) const
    {
        if (isa(InstState::Substitute))
        {
            return llvm::cast<llvm::Instruction>(graph[v])->getOperand(substitution);
        }
        return nullptr;
    }

    template <typename T>
    T get()
    {
        if constexpr (std::is_same_v<T, long>)
        {
            if (is_float)
            {
                assert(false);
            }
            return value.constant;
        }
        // else if constexpr (std::is_same_v<T, llvm::Value *>)
        // {
        //     return substitution->getOperand(0);
        // }
        else if constexpr (std::is_same_v<T, double>)
        {
            if (!is_float)
            {
                assert(false);
            }
            return value.constant_fp;
        }
        else
        {
            static_assert(false, "Invalid type");
        }
    }
};

class StatesMap
{
public:
    struct InstStateHash
    {
        size_t operator()(const InstState &state) const
        {
            if (state.isa(InstState::Zero))
            {
                return 0;
            }
            auto h1 = std::hash<int>()(state.state);
            auto h2 = std::hash<int>()(state.value.constant);
            return h1 ^ (h2 << 1);
        }
    };
    mutable std::unordered_map<InstState, std::vector<InstState>, InstStateHash> states;
    size_t vertex_num;
    InstState unknown = InstState::Unknown;

    std::vector<llvm::UserOp2Inst *> substitutions;

public:
    StatesMap(size_t _vertex_num)
    : states{}
    , vertex_num(_vertex_num)
    {
    }

    InstState &operator()(size_t u, InstState s, size_t v)
    {
        if (states[s].size() != vertex_num * vertex_num)
        {
            states[s].resize(vertex_num * vertex_num);
        }
        return states[s].at(u * vertex_num + v);
    }

    void check_substitution(size_t u, InstState s, size_t v)
    {
        if (states[s].size() != vertex_num * vertex_num)
        {
            return;
        }
        if (states[s].at(u * vertex_num + v).isa(InstState::Substitute))
        {
            // substitutions.push_back(states[s].at(u * vertex_num + v).substitution);
        }
    }
    const InstState &operator()(size_t u, InstState s, size_t v) const
    {
        if (v == -1ull)
        {
            return unknown;
        }
        if (states[s].size() != vertex_num * vertex_num)
        {
            states[s].resize(vertex_num * vertex_num);
        }
        return states[s].at(u * vertex_num + v);
    }
    StatesMap(const StatesMap &other) = delete;
    StatesMap &operator=(const StatesMap &other) = delete;
    StatesMap(StatesMap &&other)
    {
        states = std::move(other.states);
        vertex_num = other.vertex_num;
        unknown = other.unknown;
        substitutions = std::move(other.substitutions);
    }

    StatesMap &operator=(StatesMap &&other)
    {
        states = std::move(other.states);
        vertex_num = other.vertex_num;
        unknown = other.unknown;
        substitutions = std::move(other.substitutions);
        return *this;
    }

    // ~StatesMap()
    // {
    // for (auto sub : substitutions)
    // {
    //     llvm::UserOp2Inst::Destory(sub);
    // }
    // }
};
class ZeroBenefitAnalysis;
struct ZeroBenefitAnalysisResult
{
    ValueGraph graph;
    // inst id -> total benefit of the inst
    std::vector<int> benefit;
    // inst id -> direct dead vertex
    std::vector<std::vector<unsigned>> direct_dead_vertex;
    std::vector<std::vector<unsigned>> indirect_dead_vertex;
    // zero inst id -> (propogated inst id -> benefit)
    InstBenefitMap inst_benefit_map;
    StatesMap states;

public:
    ZeroBenefitAnalysisResult(ValueGraph &&_graph,
                              std::vector<int> &&_benefit,
                              std::vector<std::vector<unsigned>> &&_direct_dead_vertex,
                              std::vector<std::vector<unsigned>> &&_indirect_dead_vertex,
                              InstBenefitMap &&_inst_benefit_map,
                              StatesMap &&_states)
    : graph(std::move(_graph))
    , benefit(std::move(_benefit))
    , direct_dead_vertex(std::move(_direct_dead_vertex))
    , indirect_dead_vertex(std::move(_indirect_dead_vertex))
    , inst_benefit_map(std::move(_inst_benefit_map))
    , states(std::move(_states))
    {
    }
    ZeroBenefitAnalysisResult &operator=(ZeroBenefitAnalysisResult &&other)
    {
        graph = std::move(other.graph);
        benefit = std::move(other.benefit);
        direct_dead_vertex = std::move(other.direct_dead_vertex);
        indirect_dead_vertex = std::move(other.indirect_dead_vertex);
        inst_benefit_map = std::move(other.inst_benefit_map);
        states = std::move(other.states);
        return *this;
    }

    ZeroBenefitAnalysisResult(ZeroBenefitAnalysisResult &&other)
    : graph(std::move(other.graph))
    , benefit(std::move(other.benefit))
    , direct_dead_vertex(std::move(other.direct_dead_vertex))
    , indirect_dead_vertex(std::move(other.indirect_dead_vertex))
    , inst_benefit_map(std::move(other.inst_benefit_map))
    , states(std::move(other.states))
    {
    }

    int operator[](llvm::Value *val) const
    {
        auto id = graph[val];
        if (id == -1u)
        {
            return -1;
        }
        return benefit[id];
    }

    int operator[](int i) const { return benefit[i]; }

    size_t size() const { return benefit.size(); }

    llvm::Value *getValue(int i) const { return graph[i]; }

private:
    friend ZeroBenefitAnalysis;
    ZeroBenefitAnalysisResult &operator=(const ZeroBenefitAnalysisResult &) = delete;
    ZeroBenefitAnalysisResult(const ZeroBenefitAnalysisResult &) = delete;
};

class ZeroBenefitAnalysis : public llvm::AnalysisInfoMixin<ZeroBenefitAnalysis>
{
    friend llvm::AnalysisInfoMixin<ZeroBenefitAnalysis>;
    static llvm::AnalysisKey Key;

public:
    using Result = ZeroBenefitAnalysisResult;
    /**
     * @brief 
     * 
     * @param F 
     * @param AM 
     * @return ZeroBenefitAnalysisResult 
     */
    ZeroBenefitAnalysisResult run(llvm::Function &F, llvm::FunctionAnalysisManager &AM);

private:
    /**
     * @brief Build a subgraph for the def-use chain of the function.
     * Any pointer-type instructions except for callInst are not included in the graph.
     * 
     * @param F 
     * @param graph 
     */
    void buildGraph(llvm::Function &F, ValueGraph &graph);
};