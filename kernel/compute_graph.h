/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Jannis Harder <jix@yosyshq.com> <me@jix.one>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#ifndef COMPUTE_GRAPH_H
#define COMPUTE_GRAPH_H

#include <tuple>
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

template<
    typename Fn, // Function type (deduplicated across whole graph)
    typename Attr = std::tuple<>, // Call attributes (present in every node)
    typename SparseAttr = std::tuple<>, // Sparse call attributes (optional per node)
    typename Key = std::tuple<> // Stable keys to refer to nodes
>
struct ComputeGraph
{
    struct Ref;
private:

    // Functions are deduplicated by assigning unique ids
    idict<Fn> functions;

    struct Node {
        int fn_index;
        int arg_offset;
        int arg_count;
        Attr attr;

        Node(int fn_index, Attr &&attr, int arg_offset, int arg_count = 0)
            : fn_index(fn_index), arg_offset(arg_offset), arg_count(arg_count), attr(std::move(attr)) {}

        Node(int fn_index, Attr const &attr, int arg_offset, int arg_count = 0)
            : fn_index(fn_index), arg_offset(arg_offset), arg_count(arg_count), attr(attr) {}
    };


    std::vector<Node> nodes;
    std::vector<int> args;
    dict<Key, int> keys_;
    dict<int, SparseAttr> sparse_attrs;

public:
    template<typename Graph>
    struct BaseRef
    {
    protected:
        friend struct ComputeGraph;
        Graph *graph_;
        int index_;
        BaseRef(Graph *graph, int index) : graph_(graph), index_(index) {
            log_assert(index_ >= 0);
            check();
        }

        void check() const { log_assert(index_ < graph_->size()); }

        Node const &deref() const { check(); return graph_->nodes[index_]; }

    public:
        ComputeGraph const &graph() const { return graph_; }
        int index() const { return index_; }

        int size() const { return deref().arg_count; }

        BaseRef arg(int n) const
        {
            Node const &node = deref();
            log_assert(n >= 0 && n < node.arg_count);
            return BaseRef(graph_, graph_->args[node.arg_offset + n]);
        }

        std::vector<int>::const_iterator arg_indices_cbegin() const
        {
            Node const &node = deref();
            return graph_->args.cbegin() + node.arg_offset;
        }

        std::vector<int>::const_iterator arg_indices_cend() const
        {
            Node const &node = deref();
            return graph_->args.cbegin() + node.arg_offset + node.arg_count;
        }

        Fn const &function() const { return graph_->functions[deref().fn_index]; }
        Attr const &attr() const { return deref().attr; }

        bool has_sparse_attr() const { return graph_->sparse_attrs.count(index_); }

        SparseAttr const &sparse_attr() const
        {
            auto found = graph_->sparse_attrs.find(index_);
            log_assert(found != graph_->sparse_attrs.end());
            return found->second;
        }
    };

    using ConstRef = BaseRef<ComputeGraph const>;

    struct Ref : public BaseRef<ComputeGraph>
    {
    private:
        friend struct ComputeGraph;
        Ref(ComputeGraph *graph, int index) : BaseRef<ComputeGraph>(graph, index) {}
        Node &deref() const { this->check(); return this->graph_->nodes[this->index_]; }

    public:
        Ref(BaseRef<ComputeGraph> ref) : Ref(ref.graph_, ref.index_) {}

        void set_function(Fn const &function) const
        {
            deref().fn_index = this->graph_->functions(function);
        }

        Attr &attr() const { return deref().attr; }

        void append_arg(ConstRef arg) const
        {
            log_assert(arg.graph_ == this->graph_);
            append_arg(arg.index());
        }

        void append_arg(int arg) const
        {
            log_assert(arg >= 0 && arg < this->graph_->size());
            Node &node = deref();
            if (node.arg_offset + node.arg_count != GetSize(this->graph_->args))
                move_args(node);
            this->graph_->args.push_back(arg);
            node.arg_count++;
        }

        operator ConstRef() const
        {
            return ConstRef(this->graph_, this->index_);
        }

        SparseAttr &sparse_attr() const
        {
            return this->graph_->sparse_attrs[this->index_];
        }

        void clear_sparse_attr() const
        {
            this->graph_->sparse_attrs.erase(this->index_);
        }

        void assign_key(Key const &key) const
        {
            this->graph_->keys_.emplace(key, this->index_);
        }

    private:
        void move_args(Node &node) const
        {
            auto &args = this->graph_->args;
            int old_offset = node.arg_offset;
            node.arg_offset = GetSize(args);
            for (int i = 0; i != node.arg_count; ++i)
                args.push_back(args[old_offset + i]);
        }

    };

    bool has_key(Key const &key) const
    {
        return keys_.count(key);
    }

    dict<Key, int> const &keys() const
    {
        return keys_;
    }

    ConstRef operator()(Key const &key) const
    {
        auto it = keys_.find(key);
        log_assert(it != keys_.end());
        return (*this)[it->second];
    }

    Ref operator()(Key const &key)
    {
        auto it = keys_.find(key);
        log_assert(it != keys_.end());
        return (*this)[it->second];
    }

    int size() const { return GetSize(nodes); }

    ConstRef operator[](int index) const { return ConstRef(this, index); }
    Ref operator[](int index) { return Ref(this, index); }

    Ref add(Fn const &function, Attr &&attr)
    {
        int index = GetSize(nodes);
        int fn_index = functions(function);
        nodes.emplace_back(fn_index, std::move(attr), GetSize(args));
        return Ref(this, index);
    }

    Ref add(Fn const &function, Attr const &attr)
    {
        int index = GetSize(nodes);
        int fn_index = functions(function);
        nodes.emplace_back(fn_index, attr,  GetSize(args));
        return Ref(this, index);
    }

    template<typename T>
    Ref add(Fn const &function, Attr const &attr, T &&args)
    {
        Ref added = add(function, attr);
        for (auto arg : args)
            added.append_arg(arg);
        return added;
    }

    template<typename T>
    Ref add(Fn const &function, Attr &&attr, T &&args)
    {
        Ref added = add(function, std::move(attr));
        for (auto arg : args)
            added.append_arg(arg);
        return added;
    }

    Ref add(Fn const &function, Attr const &attr, std::initializer_list<Ref> args)
    {
        Ref added = add(function, attr);
        for (auto arg : args)
            added.append_arg(arg);
        return added;
    }

    Ref add(Fn const &function, Attr &&attr, std::initializer_list<Ref> args)
    {
        Ref added = add(function, std::move(attr));
        for (auto arg : args)
            added.append_arg(arg);
        return added;
    }

    template<typename T>
    Ref add(Fn const &function, Attr const &attr, T begin, T end)
    {
        Ref added = add(function, attr);
        for (; begin != end; ++begin)
            added.append_arg(*begin);
        return added;
    }

    void compact_args()
    {
        std::vector<int> new_args;
        for (auto &node : nodes)
        {
            int new_offset = GetSize(new_args);
            for (int i = 0; i < node.arg_count; i++)
                new_args.push_back(args[node.arg_offset + i]);
            node.arg_offset = new_offset;
        }
        std::swap(args, new_args);
    }

    void permute(std::vector<int> const &perm)
    {
        log_assert(perm.size() <= nodes.size());
        std::vector<int> inv_perm;
        inv_perm.resize(nodes.size(), -1);
        for (int i = 0; i < GetSize(perm); ++i)
        {
            int j = perm[i];
            log_assert(j >= 0 && j < GetSize(nodes));
            log_assert(inv_perm[j] == -1);
            inv_perm[j] = i;
        }
        permute(perm, inv_perm);
    }

    void permute(std::vector<int> const &perm, std::vector<int> const &inv_perm)
    {
        log_assert(inv_perm.size() == nodes.size());
        std::vector<Node> new_nodes;
        new_nodes.reserve(perm.size());
        dict<int, SparseAttr> new_sparse_attrs;
        for (int i : perm)
        {
            int j = GetSize(new_nodes);
            new_nodes.emplace_back(std::move(nodes[i]));
            auto found = sparse_attrs.find(i);
            if (found != sparse_attrs.end())
                new_sparse_attrs.emplace(j, std::move(found->second));
        }

        std::swap(nodes, new_nodes);
        std::swap(sparse_attrs, new_sparse_attrs);

        compact_args();
        for (int &arg : args)
        {
            log_assert(arg < GetSize(inv_perm));
            log_assert(inv_perm[arg] >= 0);
            arg = inv_perm[arg];
        }

        for (auto &key : keys_)
        {
            log_assert(key.second < GetSize(inv_perm));
            log_assert(inv_perm[key.second] >= 0);
            key.second = inv_perm[key.second];
        }
    }

    struct SccAdaptor
    {
    private:
        ComputeGraph const &graph_;
        std::vector<int> indices_;
    public:
        SccAdaptor(ComputeGraph const &graph) : graph_(graph)
        {
            indices_.resize(graph.size(), -1);
        }


        typedef int node_type;

        struct node_enumerator {
        private:
            friend struct SccAdaptor;
            int current, end;
            node_enumerator(int current, int end) : current(current), end(end) {}

        public:

            bool finished() const { return current == end; }
            node_type next() {
                log_assert(!finished());
                node_type result = current;
                ++current;
                return result;
            }
        };

        node_enumerator enumerate_nodes() {
            return node_enumerator(0, GetSize(indices_));
        }


        struct successor_enumerator {
        private:
            friend struct SccAdaptor;
            std::vector<int>::const_iterator current, end;
            successor_enumerator(std::vector<int>::const_iterator current, std::vector<int>::const_iterator end) :
                current(current), end(end) {}

        public:
            bool finished() const { return current == end; }
            node_type next() {
                log_assert(!finished());
                node_type result = *current;
                ++current;
                return result;
            }
        };

        successor_enumerator enumerate_successors(int index) const {
            auto const &ref = graph_[index];
            return successor_enumerator(ref.arg_indices_cbegin(), ref.arg_indices_cend());
        }

        int &dfs_index(node_type const &node) { return indices_[node]; }

        std::vector<int> const &dfs_indices() { return indices_; }
    };

};



YOSYS_NAMESPACE_END


#endif
