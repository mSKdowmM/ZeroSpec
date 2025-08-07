#pragma once

#include "boost/graph/dominator_tree.hpp"
#include "GraphBuilder.h"
#include <boost/graph/depth_first_search.hpp>
#include <boost/graph/detail/adjacency_list.hpp>
#include <boost/graph/properties.hpp>
#include <boost/graph/topological_sort.hpp>
#include <boost/graph/transitive_closure.hpp>
#include <boost/property_map/property_map.hpp>
#include <llvm/IR/Use.h>
#include <llvm/Support/Debug.h>
#include <vector>
#include "utils.h"

class DominanceInfo
{
    const ValueGraph &_graph;
    std::vector<ValueGraph::Graph::vertex_descriptor> _dom_tree;
    std::unique_ptr<bool[]> _dominates;
    std::vector<std::unordered_set<ValueGraph::Graph::vertex_descriptor>> _dom_frontier;
    span2d<bool> dominates_matrix;

    std::vector<std::vector<ValueGraph::Graph::vertex_descriptor>> dom_tree_top_down;
    std::unordered_set<ValueGraph::Graph::vertex_descriptor> _empty_set;

    class dfs_df_visitor : public boost::default_dfs_visitor
    {
        std::vector<std::unordered_set<ValueGraph::Graph::vertex_descriptor>> &dom_frontier;
        const std::vector<ValueGraph::Graph::vertex_descriptor> &dom_tree;
        const DominanceInfo &dom_info;

    public:
        dfs_df_visitor(std::vector<std::unordered_set<ValueGraph::Graph::vertex_descriptor>> &dom_frontier,
                       const std::vector<ValueGraph::Graph::vertex_descriptor> &dom_tree,
                       const DominanceInfo &dom_info)
        : dom_frontier(dom_frontier)
        , dom_tree(dom_tree)
        , dom_info(dom_info)
        {
        }
        template <typename Vertex, typename Graph>
        void start_vertex(Vertex u, const Graph &g) const
        {
        }
        template <typename Vertex, typename Graph>
        void discover_vertex(Vertex u, const Graph &g) const
        {
        }
        template <typename Vertex, typename Graph>
        void finish_vertex(Vertex u, const Graph &g) const
        {
            for (auto out_edge : boost::make_iterator_range(boost::out_edges(u, g)))
            {
                auto succ = boost::target(out_edge, g);
                if (dom_tree[succ] != u)
                {
                    dom_frontier[u].insert(succ);
                }
            }

            for (auto z : dom_info.children(u))
            {
                for (auto y : dom_frontier[z])
                {
                    if (!dom_info.dom(u, y))
                    {
                        dom_frontier[u].insert(y);
                    }
                }
            }
        }
    };

public:
    auto &get_graph() const { return _graph; }
    DominanceInfo(const ValueGraph &graph)
    : _graph(graph)
    , _dominates(std::make_unique<bool[]>(_graph.getGraph().m_vertices.size() * _graph.getGraph().m_vertices.size()))
    , dominates_matrix(_dominates.get(), _graph.getGraph().m_vertices.size(), _graph.getGraph().m_vertices.size())
    {
        _dom_tree.resize(_graph.getGraph().m_vertices.size());
        boost::lengauer_tarjan_dominator_tree(_graph.getGraph(), boost::vertex(0, _graph.getGraph()), _dom_tree.data());
        memset(_dominates.get(), 0, _graph.getGraph().m_vertices.size() * _graph.getGraph().m_vertices.size());

        ValueGraph::Graph dom_tree(_graph.getGraph().m_vertices.size());
        ValueGraph::Graph dom_closure;
        for (auto [i, idom] : llvm::enumerate(_dom_tree))
        {
            if (idom != i)
            {
                boost::add_edge(idom, i, dom_tree);
            }
        }
        boost::transitive_closure(dom_tree, dom_closure);
        for (auto edge : to_range(boost::edges(dom_closure)))
        {
            auto src = boost::source(edge, dom_closure);
            auto dst = boost::target(edge, dom_closure);
            _dominates[dst * _graph.getGraph().m_vertices.size() + src] = true;
        }

        my_dbg() << "dominates matrix built\n";
        for (int i = 0; i < _graph.getGraph().m_vertices.size(); ++i)
        {
            my_dbg() << *_graph[i] << " " << *_graph[_dom_tree[i]] << "\n";
        }
        auto root = 0;
        // my_dbg() << "root: " << root << "\n";
        _dom_frontier.resize(_graph.getGraph().m_vertices.size());
        dfs_df_visitor vis(_dom_frontier, _dom_tree, *this);
        std::vector<boost::default_color_type> colors(_graph.getGraph().m_vertices.size());
        boost::depth_first_visit(
            _graph.getGraph(),
            root,
            vis,
            boost::make_iterator_property_map(colors.begin(), boost::get(boost::vertex_index, _graph.getGraph())));

        dom_tree_top_down.resize(_graph.getGraph().m_vertices.size());
        for (auto i = 0u; i < _graph.getGraph().m_vertices.size(); ++i)
        {
            dom_tree_top_down[_dom_tree[i]].push_back(i);
        }
    }

    class children_range
    {
        decltype(boost::out_edges(0, _graph.getGraph())) _range;
        const ValueGraph &_graph;

    public:
        class Iterator
        {
            decltype(_range.first) _it;
            const ValueGraph &_graph;

        public:
            Iterator(decltype(_it) it, const ValueGraph &graph)
            : _it(it)
            , _graph(graph)
            {
            }
            auto operator*() const { return boost::target(*_it, _graph.getGraph()); }
            Iterator &operator++()
            {
                ++_it;
                return *this;
            }
            bool operator!=(const Iterator &other) const { return _it != other._it; }
        };

        auto begin() { return Iterator(_range.first, _graph); }
        auto end() { return Iterator(_range.second, _graph); }
        children_range(decltype(_range) range, const ValueGraph &graph)
        : _range(range)
        , _graph(graph)
        {
        }
    };
    auto children(llvm::Value *val) const
    {
        return children_range(boost::out_edges(_graph[val], _graph.getGraph()), _graph);
    }
    auto children(unsigned long u) const { return children_range(boost::out_edges(u, _graph.getGraph()), _graph); }

    // nodes immediately dominated by u
    auto &get_idomed_by(unsigned long u) const { return dom_tree_top_down[u]; }

    unsigned long parent(unsigned long u) const { return _dom_tree[u]; }

    bool dom(long va, long vb) const { return va == vb || dominates_matrix(va, vb); }
    bool dom(llvm::Value *a, llvm::Value *b) const
    {
        auto va = _graph[a];
        auto vb = _graph[b];
        if (va == -1)
        {
            my_dbg() << "a not in graph\n";
            my_dbg() << "a: " << *a << "\n";
            throw nullptr;
        }
        if (vb == -1)
        {
            return false;
            my_dbg() << "b not in graph\n";
            my_dbg() << "b: " << b << b->getValueID() << "\n";
            throw nullptr;
        }
        return a == b || dominates_matrix(va, vb);
    }

    bool sdom(llvm::Value *a, llvm::Value *b) const
    {
        auto va = _graph[a];
        auto vb = _graph[b];
        return dominates_matrix(va, vb) && va != vb;
    }

    bool idom(llvm::Value *a, llvm::Value *b) const
    {
        auto va = _graph[a];
        auto vb = _graph[b];
        return _dom_tree[vb] == va;
    }
    bool idom(unsigned long a, unsigned long b) const { return _dom_tree[b] == a; }
    const std::unordered_set<ValueGraph::Graph::vertex_descriptor> &getDomFrontier(llvm::Value *val) const
    {
        if (!_graph.contains(val))
        {
            my_dbg() << "val not in graph\n";
            my_dbg() << "val: " << *val << "\n";
            return _empty_set;
        }
        return _dom_frontier.at(_graph[val]);
    }
    unsigned long operator[](llvm::Value *val) const { return _graph[val]; }
    llvm::Value *operator[](unsigned long id) const { return _graph[id]; }
};