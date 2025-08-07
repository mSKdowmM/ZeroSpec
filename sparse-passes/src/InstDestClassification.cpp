#include "InstDestClassification.h"
#include "llvm/IR/Instructions.h"
#include <unordered_map>
#include <llvm/ADT/iterator_range.h>
#include <set>
#include <vector>
#include <boost/graph/strong_components.hpp>
#include <boost/graph/topological_sort.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/property_maps/container_property_map.hpp>
using namespace llvm;
using std::set;
using std::unordered_map;
using std::vector;
InstDestClassificationResult::InstDestClassificationResult(InstDestClassificationResult &&r)
{
    this->value2type = std::move(r.value2type);
}
InstDestClassificationResult &InstDestClassificationResult::operator=(InstDestClassificationResult &&r)
{
    this->value2type = std::move(r.value2type);
    return *this;
}

AnalysisKey InstDestClassification::Key;
InstDestClassificationResult::InstDestClassificationResult(std::unordered_map<llvm::Value *, int> &&_v2t)
{
    this->value2type = std::move(_v2t);
}

InstDestClassificationResult::InstType InstDestClassificationResult::getType(int id, Value *v)
{
    if (id == 0)
    {
        return INDEX_TYPE;
    }
    if (!isa<Instruction>(v))
    {
        return EMPTY_TYPE;
    }
    if (isa<StoreInst, CallInst, ReturnInst>(v))
    {
        return VALUE_TYPE;
    }
    if (isa<BranchInst, SelectInst>(v))
    {
        return BRANCH_TYPE;
    }
    if (isa<GetElementPtrInst>(v))
    {
        return INDEX_TYPE;
    }
    return EMPTY_TYPE;
}

InstDestClassificationResult InstDestClassification::run(Function &F, FunctionAnalysisManager &AM)
{
    using InstType = InstDestClassificationResult::InstType;
    enum
    {
        PRT_INDEX,
        SPECIAL_VERTEX_NUM
    };
    InstDestClassificationResult res;
    using VertexProperty = Value *;

    using Graph = boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS>;
    using vertex_t = boost::graph_traits<Graph>::vertex_descriptor;

    Graph use_graph;
    unordered_map<VertexProperty, int> inst2id;
    vector<Value *> id2inst;
    for (int i = 0; i < SPECIAL_VERTEX_NUM; ++i)
    {
        boost::add_vertex(use_graph);
        id2inst.push_back(nullptr);
    }

    for (auto &arg : F.args())
    {
        auto vid = boost::add_vertex(use_graph);
        id2inst.push_back(&arg);
        inst2id.emplace(&arg, vid);
    }

    for (auto &bb : F)
    {
        for (auto &inst : bb)
        {
            auto vid = boost::add_vertex(use_graph);
            id2inst.push_back(&inst);
            inst2id.emplace(&inst, vid);
        }
    }

    for (const auto &p : inst2id)
    {
        auto inst = dyn_cast<Instruction>(p.first);
        if (!inst)
        {
            continue;
        }

        for (const auto &[i, use] : llvm::enumerate(inst->operands()))
        {
            int vid = inst2id[inst];
            if (!isa_and_present<Instruction>(use.get()))
            {
                continue;
            }
            int uid = inst2id[use.get()];
            if ((i > 0 && isa<StoreInst>(inst)) || isa<LoadInst>(inst) || (i == 0 && isa<GetElementPtrInst>(inst)) ||
                (!isa<CallInst>(inst) && inst->getType()->isPointerTy()))
            {
                boost::add_edge(uid, PRT_INDEX, use_graph);
            }
            else
            {
                boost::add_edge(uid, vid, use_graph);
            }
        }
    }
    // using ComponentMap = boost::container_property_map<Graph, int, unordered_map<int,int>>;
    using ComponentMap = vector<std::size_t>;
    // graph vertex id to strong component id
    ComponentMap sc_id2label(boost::num_vertices(use_graph));
    int sc_num =
        boost::strong_components(use_graph,
                                 boost::make_iterator_property_map(
                                     sc_id2label.begin(), boost::get(boost::vertex_index, use_graph), sc_id2label[0]));

    // strong component graph
    Graph sc_graph(sc_num);

    // strong component id to vertex id
    vector<set<int>> sc_label2id(sc_num);
    for (auto [i, label] : enumerate(sc_id2label))
    {
        sc_label2id[label].insert(i);
    }
    auto visited = std::make_unique<bool[]>(sc_num);
    for (auto &u_set : sc_label2id)
    {
        memset(visited.get(), 0, sc_num);
        for (auto uid : u_set)
        {
            auto adj_list = boost::adjacent_vertices(uid, use_graph);
            int sc_uid = sc_id2label[uid];
            visited[sc_uid] = true;
            for (auto vid : llvm::make_range(adj_list))
            {
                int sc_vid = sc_id2label[vid];
                if (!visited[sc_vid])
                {
                    visited[sc_vid] = true;
                    boost::add_edge(sc_uid, sc_vid, sc_graph);
                }
            }
        }
    }
    vector<size_t> sc_topo;
    boost::topological_sort(sc_graph,
                            // boost::make_iterator_property_map(sc_topo.begin(), boost::identity_property_map()));
                            std::back_insert_iterator(sc_topo));

    vector<int> sc_label2type(sc_num, InstType::EMPTY_TYPE);
    unordered_map<Value *, int> inst2type;
    for (auto sc_uid : sc_topo)
    {
        int sc_u_type = InstType::EMPTY_TYPE;
        auto &u_set = sc_label2id[sc_uid];
        // my_dbg() << "--------------------------------\n";
        // my_dbg() << "sc_uid: " << sc_uid << "\n";
        if (u_set.size() != 1 || true)
        {
            for (auto uid : u_set)
            {
                if (u_set.size() != 1)
                {
                    sc_u_type |= InstDestClassificationResult::getType(uid, id2inst[uid]);
                }
                // if (uid != 0)
                //     my_dbg() << "utype: " << sc_u_type << " uid: " << uid << " inst: " << *id2inst[uid] << "\n";
                // else
                //     my_dbg() << "utype: " << sc_u_type << " uid: " << uid << " inst: "
                //            << "nullptr\n";
            }
        }
        auto range = llvm::make_range(boost::adjacent_vertices(sc_uid, sc_graph));
        for (auto sc_vid : range)
        {
            // my_dbg() << "sc_vid: " << sc_vid << " sc_vtype: " << sc_label2type[sc_vid] << "\n";
            sc_u_type |= sc_label2type[sc_vid];
            auto &v_set = sc_label2id[sc_vid];
            if (v_set.size() == 1 || true)
            {
                for (auto vid : v_set)
                {
                    if (v_set.size() == 1)
                    {
                        sc_u_type |= InstDestClassificationResult::getType(vid, id2inst[vid]);
                    }
                    // if (vid != 0)
                    //     my_dbg() << "utype: " << sc_u_type << " vid: " << vid << " inst: " << *id2inst[vid] << "\n";
                    // else
                    //     my_dbg() << "utype: " << sc_u_type << " vid: " << vid << " inst: "
                    //            << "nullptr\n";
                }
            }
        }
        sc_label2type[sc_uid] = sc_u_type;
        for (auto uid : sc_label2id[sc_uid])
        {
            inst2type[id2inst[uid]] = sc_u_type;
        }
    }

    return InstDestClassificationResult(std::move(inst2type));
}
