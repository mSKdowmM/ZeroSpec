#pragma once
#include "boost/graph/graph_selectors.hpp"
#include "boost/graph/strong_components.hpp"
#include <boost/graph/graph_traits.hpp>
#include "llvm/IR/Value.h"
#include <boost/graph/adjacency_list.hpp>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/Debug.h>
#include <unordered_map>
#include <utility>
#include <vector>
#include <set>
#include "boost/graph/transitive_closure.hpp"
#include "utils.h"
#include <developing.h>
class ValueGraph
{
public:
    using VertexProperty = llvm::Value *;
    using Graph = boost::adjacency_list<boost::vecS, boost::vecS, boost::bidirectionalS>;
    using vertex_t = boost::graph_traits<Graph>::vertex_descriptor;
    using ComponentMap = std::vector<std::size_t>;

private:
    Graph _graph;
    // map from vertex id to llvm::Value*
    std::vector<VertexProperty> id2value;
    // map from llvm::Value* to vertex id
    std::unordered_map<VertexProperty, vertex_t> value2id;

    // strong connected components graph
    Graph _sc_graph;
    // give any strong components a label, make bidirection-map between label and vertex id
    ComponentMap sc_id2label;
    std::vector<std::set<vertex_t>> sc_label2id;

    mutable std::vector<char> reachability;
    mutable Graph _closure;

public:
    ValueGraph(const ValueGraph &) = default;
    ValueGraph &operator=(const ValueGraph &) = default;
    ValueGraph(ValueGraph &&_other)
    : _graph(std::move(_other._graph))
    , id2value(std::move(_other.id2value))
    , value2id(std::move(_other.value2id))
    , _sc_graph(std::move(_other._sc_graph))
    , sc_id2label(std::move(_other.sc_id2label))
    , sc_label2id(std::move(_other.sc_label2id))
    , reachability(std::move(_other.reachability))
    , _closure(std::move(_other._closure))
    {
    }

    ValueGraph &operator=(ValueGraph &&_other)
    {
        _graph = std::move(_other._graph);
        id2value = std::move(_other.id2value);
        value2id = std::move(_other.value2id);
        _sc_graph = std::move(_other._sc_graph);
        sc_id2label = std::move(_other.sc_id2label);
        sc_label2id = std::move(_other.sc_label2id);
        reachability = std::move(_other.reachability);
        _closure = std::move(_other._closure);
        return *this;
    }
    auto &closure() { return _closure; }

    ValueGraph() = default;
    ValueGraph(const std::vector<llvm::Value *> &values)
    {
        for (auto *value : values)
        {
            auto vertex = boost::add_vertex(_graph);
            id2value.push_back(value);
            value2id[value] = vertex;
        }
    }

    span2d<bool> get_reachability() const
    {
        if (reachability.empty())
        {
            build_reachability_matrix();
        }
        return span2d<bool>((bool *)reachability.data(), id2value.size(), id2value.size());
    }

    bool reachable(unsigned long src, unsigned long dst) const
    {
        if (reachability.empty())
        {
            build_reachability_matrix();
        }
        return reachability[src * id2value.size() + dst];
    }
    bool reachable(VertexProperty src, VertexProperty dst) const
    {
        if (reachability.empty())
        {
            build_reachability_matrix();
        }
        if (value2id.find(src) == value2id.end() || value2id.find(dst) == value2id.end())
        {
            my_dbg() << "src or dst not in graph\n";
            my_dbg() << "src: " << *src << "\n";
            my_dbg() << "dst: " << *dst << "\n";
        }
        auto src_id = value2id.at(src);
        if (value2id.find(dst) == value2id.end())
        {
            my_dbg() << "dst not in graph\n";
            my_dbg() << "dst: " << *dst << "\n";
        }
        auto dst_id = value2id.at(dst);
        return reachability[src_id * id2value.size() + dst_id];
    }

    auto value_begin() const { return id2value.begin(); }
    auto value_end() const { return id2value.end(); }

    const auto &sc_label2id_map() const { return sc_label2id; }
    const auto &sc_id2label_map() const { return sc_id2label; }

    struct value_range_t
    {
        const ValueGraph *graph;
        value_range_t(const ValueGraph *graph)
        : graph(graph)
        {
        }
        auto begin() const { return graph->value_begin(); }
        auto end() const { return graph->value_end(); }
    };

    auto value_range() const { return value_range_t(this); }

    const Graph &getGraph() const { return _graph; }
    const Graph &getSCGraph() const { return _sc_graph; }

    bool contains(VertexProperty value) const { return value2id.find(value) != value2id.end(); }

    vertex_t operator[](VertexProperty value) const
    {
        auto iter = value2id.find(value);
        if (iter == value2id.end())
        {
            return -1;
        }
        else
        {
            return iter->second;
        }
    }

    VertexProperty operator[](vertex_t vertex) const { return id2value[vertex]; }
    vertex_t addVertex(VertexProperty value)
    {
        auto vertex = boost::add_vertex(_graph);
        id2value.push_back(value);
        value2id[value] = vertex;
        return vertex;
    }
    void addEdge(VertexProperty src, VertexProperty dst) { boost::add_edge(value2id[src], value2id[dst], _graph); }
    void addEdge(vertex_t src, vertex_t dst) { boost::add_edge(src, dst, _graph); }
    void addEdges(VertexProperty src, const std::vector<VertexProperty> &dsts)
    {
        for (auto *dst : dsts)
        {
            addEdge(src, dst);
        }
    }
    void addEdges(vertex_t src, const std::vector<vertex_t> &dsts)
    {
        for (auto dst : dsts)
        {
            addEdge(src, dst);
        }
    }
    void addEdges(const std::vector<VertexProperty> &srcs, VertexProperty dst)
    {
        for (auto *src : srcs)
        {
            addEdge(src, dst);
        }
    }
    void addEdges(const std::vector<vertex_t> &srcs, vertex_t dst)
    {
        for (auto src : srcs)
        {
            addEdge(src, dst);
        }
    }
    void addEdges(const std::vector<VertexProperty> &srcs, const std::vector<VertexProperty> &dsts)
    {
        for (auto *src : srcs)
        {
            addEdges(src, dsts);
        }
    }
    void addEdges(const std::vector<vertex_t> &srcs, const std::vector<vertex_t> &dsts)
    {
        for (auto src : srcs)
        {
            addEdges(src, dsts);
        }
    }

    void removeEdge(VertexProperty src, VertexProperty dst)
    {
        boost::remove_edge(value2id[src], value2id[dst], _graph);
    }

    void build_scc()
    {
        if (boost::num_vertices(_graph) == 0)
        {
            return;
        }
        sc_id2label.resize(boost::num_vertices(_graph));
        int sc_num =
            boost::strong_components(_graph,
                                     boost::make_iterator_property_map(
                                         sc_id2label.begin(), boost::get(boost::vertex_index, _graph), sc_id2label[0]));
        _sc_graph = Graph(sc_num);
        sc_label2id.resize(sc_num);
        for (auto [i, label] : llvm::enumerate(sc_id2label))
        {
            sc_label2id[label].insert(i);
        }

        auto visited = std::make_unique<bool[]>(sc_num);
        for (auto &u_set : sc_label2id)
        {
            memset(visited.get(), 0, sc_num);
            for (auto uid : u_set)
            {
                auto adj_list = boost::adjacent_vertices(uid, _graph);
                int sc_uid = sc_id2label[uid];
                visited[sc_uid] = true;
                for (auto vid : llvm::make_range(adj_list))
                {
                    int sc_vid = sc_id2label[vid];
                    if (!visited[sc_vid])
                    {
                        visited[sc_vid] = true;
                        boost::add_edge(sc_uid, sc_vid, _sc_graph);
                    }
                }
            }
        }
    }

    std::vector<Graph::vertex_descriptor> build_topo() const
    {
        std::vector<Graph::vertex_descriptor> topo;
        boost::topological_sort(_graph, std::back_inserter(topo));
        return topo;
    }

private:
    void build_reachability_matrix() const
    {
        auto vertex_num = boost::num_vertices(getGraph());
        reachability.resize(vertex_num * vertex_num);
        // memset(reachability.data(), 0, vertex_num * vertex_num * sizeof(bool));

        auto r = span2d<bool>((bool *)reachability.data(), vertex_num, vertex_num);
        // ValueGraph::Graph _closure;
        boost::transitive_closure(getGraph(), _closure);
        for (size_t u = 0; u < vertex_num; ++u)
        {
            r(u, u) = 1;
        }
        for (size_t u = 0; u < vertex_num; ++u)
        {
            for (auto e : to_range(boost::out_edges(u, _closure)))
            {
                auto v = boost::target(e, _closure);
                r(u, v) = 1;
            }
        }
    }
};

inline void build_basicblock_graph(llvm::Function &F, ValueGraph &graph)
{
    for (auto &block : F)
    {
        graph.addVertex(&block);
    }
    for (auto &block : F)
    {
        if (block.getTerminator() == nullptr)
        {
            continue;
        }
        for (auto i = 0u; i < block.getTerminator()->getNumSuccessors(); ++i)
        {
            auto b = block.getTerminator()->getSuccessor(i);
            graph.addEdge(&block, b);
        }
    }
}
inline void build_basicblock_graph_without_backedge(llvm::Function &F, ValueGraph &graph, const llvm::DominatorTree &dt)
{
    for (auto &block : F)
    {
        graph.addVertex(&block);
    }
    for (auto &block : F)
    {
        if (block.getTerminator() == nullptr)
        {
            continue;
        }
        for (auto i = 0u; i < block.getTerminator()->getNumSuccessors(); ++i)
        {
            auto b = block.getTerminator()->getSuccessor(i);
            if (dt.dominates(b, &block))
            {
                continue;
            }
            graph.addEdge(&block, b);
        }
    }
}