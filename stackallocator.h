#include <iostream>
#include <iterator>
#include <memory>
#include <type_traits>
#include <functional>
#include <new>


template<size_t NoBytes>
class StackStorage {
private:
    char storage_[NoBytes];
    char* free_memory_suffix_ptr_ = storage_;

    void allignFreeMemorySuffix(size_t alignment, size_t size) {
        void* free_memory_suffix_ptr_tmp = free_memory_suffix_ptr_;
        size_t space_tmp = getFreeSpace();
        std::align(alignment, size, free_memory_suffix_ptr_tmp, space_tmp);
        free_memory_suffix_ptr_ = static_cast<char*>(free_memory_suffix_ptr_tmp);
    }

public:
    StackStorage() = default;
    StackStorage(const StackStorage&) = delete;
    StackStorage& operator=(const StackStorage&) = delete;

    size_t getFreeSpace() const {
        return (storage_ + NoBytes) - free_memory_suffix_ptr_;
    }

    char* getBytes(size_t alignment, size_t no_bytes_required) {
        allignFreeMemorySuffix(alignment, no_bytes_required);
        if (getFreeSpace() < no_bytes_required) {
            throw std::bad_alloc();
        }
        char* result = free_memory_suffix_ptr_;
        free_memory_suffix_ptr_ += no_bytes_required;
        return result;
    }

    void freeBytes([[maybe_unused]] char* bytes_ptr, [[maybe_unused]] size_t no_bytes_to_free) {}
};


template<typename T, size_t NoBytes>
class StackAllocator {
public:
    using StackStorageT = StackStorage<NoBytes>;
    StackStorageT* stack_storage_;
public:
    using propagate_on_container_copy_assignment = std::true_type;
    using propagate_on_container_move_assignment = std::true_type;
    using propagate_on_container_swap = std::true_type;
    using value_type = T;

    StackAllocator(StackStorageT& stack_storage): stack_storage_(&stack_storage) {}

    template<typename U>
    StackAllocator(const StackAllocator<U, NoBytes>& that): stack_storage_(that.stack_storage_) {}

    value_type* allocate(size_t no_objects) {
        return reinterpret_cast<value_type*>(stack_storage_->getBytes(alignof(T), no_objects * sizeof(T)));
    }

    void deallocate(value_type* objects_ptr, size_t no_objects) {
        return stack_storage_->freeBytes(reinterpret_cast<char*>(objects_ptr), no_objects * sizeof(T));
    }

    template<typename U>
    struct rebind {
        using other = StackAllocator<U, NoBytes>;
    };

    bool operator==(const StackAllocator& other) const {
        return stack_storage_ == other.stack_storage_;
    }

    bool operator!=(const StackAllocator& other) const {
        return ~(operator==(other));
    }
};


namespace {
    struct BaseNode {
        BaseNode* prev = nullptr;
        BaseNode* next = nullptr;

        BaseNode() {}
        BaseNode(BaseNode* prev, BaseNode* next): prev(prev), next(next) {}
    };

    template<typename T>
    struct Node : BaseNode {
        T value = T();

        Node(): BaseNode() {}
        Node(BaseNode* prev, BaseNode* next): BaseNode(prev, next) {}
        Node(const T& value): value(value) {}
        Node(BaseNode* prev, BaseNode* next, const T& value): BaseNode(prev, next), value(value) {}

        using Base = BaseNode;
    };
}

namespace {
    template<typename T, typename NodeAllocator>
    class BasicList : private NodeAllocator {
    private:
        NodeAllocator& getAllocatorReference() {
            return static_cast<NodeAllocator&>(*this);
        }

        const NodeAllocator& getAllocatorReference() const {
            return removeConstness()->getAllocatorReference();
        }

        using AllocatorTraits = std::allocator_traits<NodeAllocator>;
        using NodeType = typename AllocatorTraits::value_type;
        using BaseNodeType = typename NodeType::Base;

        BaseNodeType root_ = BaseNodeType{ &root_, &root_ };
        size_t size_ = 0;

        static void connectConsecutiveNodes(BaseNodeType* node, BaseNodeType* following_node) {
            node->next = following_node;
            following_node->prev = node;
        }

        void destroyNodes(NodeType* node, size_t no_nodes_to_destroy_forward) {
            while (no_nodes_to_destroy_forward--) {
                NodeType* tmp = node;
                node = node->next;
                AllocatorTraits::destroy(*this, node);
            }
        }

        template<typename U, typename StoredNodeType>
        class BasicIterator {
        public:
            using iterator_category = std::bidirectional_iterator_tag;
            using value_type = U;
            using pointer = value_type*;
            using reference = value_type&;
            using difference_type = ptrdiff_t;

        private:
            using StoredBaseNodeType = typename StoredNodeType::Base;
            StoredBaseNodeType* base_node_; 
            friend BasicList;

            explicit BasicIterator(StoredBaseNodeType* base_node): base_node_(base_node) {}

            StoredNodeType* getNodePointer() const {
                return static_cast<StoredNodeType*>(base_node_);
            }

        public:
            value_type& operator*() const {
                return getNodePointer()->value;
            }

            pointer operator->() const {
                return &operator*();
            }

            BasicIterator& operator++() {
                base_node_ = base_node_->next;
                return *this;
            }

            BasicIterator operator++(int) {
                auto result = *this;
                operator++();
                return result;
            }

            BasicIterator& operator--() {
                base_node_ = base_node_->prev;
                return *this;
            }

            BasicIterator operator--(int) {
                auto result = *this;
                operator--();
                return result;
            }

            operator BasicIterator<const U, StoredNodeType>() const {
                return BasicIterator<const U, StoredNodeType>(base_node_);
            }

            bool operator==(const BasicIterator& other) const {
                return base_node_ == other.base_node_;
            }

            bool operator!=(const BasicIterator& other) const {
                return (!operator==(other));
            }
        };

        NodeType* allocateNode() {
            return AllocatorTraits::allocate(*this, 1);
        }

        void deallocateNode(NodeType* node) {
            AllocatorTraits::deallocate(*this, node, 1);
        }

        void destroyNode(NodeType* node) {
            AllocatorTraits::destroy(*this, node);
        }

        void destroyAndDeallocateNode(NodeType* node) {
            destroyNode(node);
            deallocateNode(node);
        }

        void cleanList() {
            while (!empty()) {
                pop_back();
            }
        }

        BasicList* removeConstness() const {
            return const_cast<BasicList*>(this);
        }

        static void swapRoots(BaseNode& lhs_root, BaseNode& rhs_root) {
            BaseNode* new_rhs_root_next;
            BaseNode* new_rhs_root_prev;
            if (lhs_root.next == &lhs_root) {
                new_rhs_root_next = new_rhs_root_prev = &rhs_root;
            } else {
                new_rhs_root_next = lhs_root.next;
                new_rhs_root_prev = lhs_root.prev;
            }

            BaseNode* new_this_root_next;
            BaseNode* new_this_root_prev;
            if (rhs_root.next == &rhs_root) {
                new_this_root_next = new_this_root_prev = &lhs_root;
            } else {
                new_this_root_next = other.lhs_root.next;
                new_this_root_prev = other.lhs_root.prev;
            }

            connectConsecutiveNodes(new_this_root_prev, &lhs_root);
            connectConsecutiveNodes(&lhs_root, new_this_root_next);

            connectConsecutiveNodes(new_rhs_root_prev, &rhs_root);
            connectConsecutiveNodes(&rhs_root, new_rhs_root_next);
        }

        template<bool SwapAllocators>
        void swapImpl(BasicList& other) {
            swapRoots(root_, other.root_);
            std::swap(size_, other.size_);
            if constexpr (SwapAllocators) {
                std::swap(getAllocatorReference(), other.getAllocatorReference());
            }
        }

    public:
        using iterator = BasicIterator<T, NodeType>;
        using const_iterator = BasicIterator<const T, NodeType>;
        using reverse_iterator = std::reverse_iterator<iterator>;
        using const_reverse_iterator = std::reverse_iterator<const_iterator>;

    private:
        struct DefaultBackEmplacer {
            void operator()(BasicList& target) {
                target.emplace_back();
            }
        };

        struct ValueBackEmplacer {
            const T& value;
            void operator()(BasicList& target) {
                target.emplace_back(value);
            }
        };

        struct IteratorBackEmplacer {
            const_iterator it;
            void operator()(BasicList& target) {
                target.emplace_back(*it++);
            }
        };

        template<typename BackEmplacer>
        BasicList(size_t no_objects, BackEmplacer back_emplacer, const NodeAllocator& alloc)
        : NodeAllocator(alloc) {
            while (no_objects--) {
                try {
                    back_emplacer(*this);
                } catch(...) {
                    cleanList();
                    throw;
                }
            }
        }

    public:
        BasicList() = default;

        BasicList(size_t no_objects, const NodeAllocator& alloc = NodeAllocator())
            : BasicList(no_objects, DefaultBackEmplacer{}, alloc) {}

        BasicList(size_t no_objects, const T& value, const NodeAllocator& alloc = NodeAllocator())
            : BasicList(no_objects, ValueBackEmplacer{ value }, alloc){}


        BasicList(const NodeAllocator& alloc): NodeAllocator(alloc) {}

        BasicList(const BasicList& other, const NodeAllocator& alloc)
            : BasicList(other.size(), IteratorBackEmplacer{ other.cbegin() }, alloc) {}

        BasicList(const BasicList& other)
            : BasicList(other, AllocatorTraits::select_on_container_copy_construction(other.get_allocator())) {}

        BasicList& operator=(const BasicList& other) {
            const NodeAllocator& new_alloc = 
                (AllocatorTraits::propagate_on_container_copy_assignment::value ? other : *this).get_allocator();
            BasicList(other, new_alloc).swapImpl<true>(*this);
            return *this;
        }

        void swap(BasicList& other) {
            swapImpl<AllocatorTraits::propagate_on_container_swap::value>(other);
        }

        iterator begin() {
            return iterator(root_.next);
        }

        const_iterator cbegin() const {
            return removeConstness()->begin();
        }

        const_iterator begin() const {
            return cbegin();
        }

        iterator end() {
            return iterator(&root_);
        }

        const_iterator end() const {
            return cend();
        }

        const_iterator cend() const {
            return removeConstness()->end();
        }

        reverse_iterator rbegin() {
            return reverse_iterator(end());
        }

        const_reverse_iterator rbegin() const {
            return crbegin();
        }

        const_reverse_iterator crbegin() const {
            return removeConstness()->rbegin();
        }

        reverse_iterator rend() {
            return reverse_iterator(begin());
        }

        const_reverse_iterator rend() const {
            return crend();
        }

        const_reverse_iterator crend() const {
            return removeConstness()->rend();
        }

        using allocator_type = NodeAllocator;
        allocator_type get_allocator() const { return getAllocatorReference(); }

        size_t size() const noexcept {
            return size_;
        }

        bool empty() const noexcept {
            return size() == 0;
        }

        template<typename... Args>
        iterator emplace(const_iterator pos, Args&&... args) {
            NodeType* new_node = allocateNode();
            try {
                AllocatorTraits::construct(*this, new_node, std::forward<Args>(args)...);
            } catch(...) {
                deallocateNode(new_node);
                throw;
            }
            BaseNode* node_before = pos.base_node_->prev;
            BaseNode* node_after  = pos.base_node_;
            connectConsecutiveNodes(node_before, new_node);
            connectConsecutiveNodes(new_node, node_after);
            ++size_;
            return iterator(new_node);
        }

        template<typename... Args>
        iterator emplace_back(Args&&... args) {
            return emplace(end(), std::forward<Args>(args)...);
        }

        template<typename... Args>
        iterator emplace_front(Args&&... args) {
            return emplace(begin(), std::forward<Args>(args)...);
        }

        void push_back(const T& value) {
            emplace(end(), value);
        }

        void push_front(const T& value) {
            emplace(begin(), value);
        }

        iterator insert(const_iterator pos, const T& value) {
            return emplace(pos, value);
        }

        iterator erase(const_iterator pos) {
            NodeType* target_node = pos.getNodePointer();
            BaseNode* node_before = target_node->prev;
            BaseNode* node_after = target_node->next;
            destroyAndDeallocateNode(target_node);
            connectConsecutiveNodes(node_before, node_after);
            --size_;
            return iterator(node_after);
        }

        void pop_back() {
            erase(std::prev(end()));
        }

        void pop_front() {
            erase(begin());
        }

        ~BasicList() {
            cleanList();
        }
    };
}

template<typename T, typename Allocator = std::allocator<T>>
using List = BasicList<T, typename std::allocator_traits<Allocator>::template rebind_alloc<Node<T>>>;

