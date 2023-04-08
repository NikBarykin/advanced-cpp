#include <cstddef>
#include <cassert>
#include <iostream>
#include <stdexcept>
#include <array>
#include <functional>
#include <algorithm>
#include <iterator>
#include <cmath>


template<typename T>
class YieldIterator {
private:
    T const* m_value_ptr = nullptr;
public:
    using iterator_category = std::input_iterator_tag;
    using value_type = T;
    using reference = value_type&;
    using pointer = value_type*;
    YieldIterator(): m_value_ptr(nullptr) {}
    explicit YieldIterator(const T& value): m_value_ptr(&value) {}
    constexpr auto& operator++() { return *this; }
    constexpr auto operator++(int) { return *this; };
    bool operator==(const YieldIterator& other) const = default;
    constexpr auto operator*() const { return *m_value_ptr; }
};

template<typename T>
YieldIterator<T> makeYieldIterator(const T& value) {
    return YieldIterator<T>(value);
}


template<size_t BytesInChunk>
class ArrayOfChunks {
private:
    using Chunk = std::array<char, BytesInChunk>;
    using ChunkHolder = Chunk*;

    class ArrayOfChunkHolders {
    private:
        ChunkHolder* m_data_begin = nullptr;
        ChunkHolder* m_data_end = nullptr;
        ChunkHolder* m_holders_begin = nullptr;
        ChunkHolder* m_holders_end = nullptr;

        void extend() {
            ArrayOfChunkHolders tmp(empty() ? static_cast<size_t>(1) : size());
            std::copy(begin(), end(), tmp.begin());
            swap(tmp);
        }

    public:
        using iterator = ChunkHolder*;
        using const_iterator = ChunkHolder const*;

        ArrayOfChunkHolders() = default;
        ArrayOfChunkHolders(size_t n)
            //NOLINTNEXTLINE
            : m_data_begin(new ChunkHolder[3 * n])
            //NOLINTNEXTLINE
            , m_data_end(m_data_begin + 3 * n)
            , m_holders_begin(m_data_begin + n)
            , m_holders_end(m_holders_begin + n) {}

        ArrayOfChunkHolders(const ArrayOfChunkHolders&) = delete;
        ArrayOfChunkHolders& operator=(const ArrayOfChunkHolders&) = delete;

        void swap(ArrayOfChunkHolders& that) {
            std::swap(m_data_begin, that.m_data_begin);
            std::swap(m_data_end, that.m_data_end);
            std::swap(m_holders_begin, that.m_holders_begin);
            std::swap(m_holders_end, that.m_holders_end);
        }

        iterator begin() {
            return m_holders_begin;
        }

        const_iterator begin() const {
            return m_holders_begin;
        }

        iterator end() {
            return m_holders_end;
        }

        const_iterator end() const {
            return m_holders_end;
        }

        const_iterator cbegin() const noexcept {
            return begin();
        }

        const_iterator cend() const noexcept {
            return end();
        }

        size_t size() const noexcept {
            return static_cast<size_t>(end() - begin());
        }

        bool empty() const noexcept {
            return begin() == end();
        }

        size_t capacity() const noexcept {
            return static_cast<size_t>(m_data_end - m_data_begin);
        }

        void addHolderAtBack() {
            if (m_holders_end == m_data_end) {
                extend();
            }
            ++m_holders_end;
        }

        void addHolderAtFront() {
            if (m_holders_begin == m_data_begin) {
                extend();
            }
            --m_holders_begin;
        }

        const ChunkHolder& operator[](size_t pos) {
            return *(begin() + pos);
        }

        ChunkHolder& front() {
            return *begin();
        }

        ChunkHolder& back() {
            return *std::prev(end());
        }

        const ChunkHolder& front() const {
            return *begin();
        }

        const ChunkHolder& back() const {
            return *std::prev(end());
        }

        ~ArrayOfChunkHolders() {
            delete[] m_data_begin;
        }
    };

    ArrayOfChunkHolders m_chunk_holders;

    void freeFirstNHolders(size_t n) noexcept {
        for (size_t i = 0; i < n; ++i) {
            delete m_chunk_holders[i];
        }
    }

private:
    using chunk_holder_iterator = typename ArrayOfChunkHolders::iterator;
    using const_chunk_holder_iterator = typename ArrayOfChunkHolders::const_iterator;

    template<typename ChunkHolderIteratorT>
    class IteratorBase {
    private:
        ChunkHolderIteratorT m_chunk_holder_it;

    public:
        using iterator_category = std::random_access_iterator_tag;
        using value_type = std::remove_pointer_t<typename std::iterator_traits<ChunkHolderIteratorT>::value_type>;
        using difference_type = std::ptrdiff_t;
        using reference = value_type&;
        using pointer = value_type*;

        explicit IteratorBase(ChunkHolderIteratorT chunk_holder_it)
            : m_chunk_holder_it(chunk_holder_it) {}
        IteratorBase& operator++() { 
            ++m_chunk_holder_it;
            return *this;
        }
        IteratorBase operator++(int) {
            IteratorBase result = *this;
            operator++();
            return result;
        }
        IteratorBase& operator--() { 
            --m_chunk_holder_it;
            return *this;
        }
        IteratorBase operator--(int) {
            IteratorBase result = *this;
            operator--();
            return result;
        }
        IteratorBase& operator+=(difference_type shift) { 
            m_chunk_holder_it += shift; 
            return *this;
        }

        IteratorBase& operator-=(difference_type n) {
            return operator+=(-n);
        }

        auto operator<=>(const IteratorBase&) const = default;

        difference_type operator-(IteratorBase that) const {
            return m_chunk_holder_it - that.m_chunk_holder_it;
        }

        IteratorBase operator+(difference_type n) const {
            IteratorBase result = *this;
            result += n;
            return result;
        }

        IteratorBase operator-(difference_type n) const {
            return operator+(-n);
        }

        reference operator*() const {
            return **m_chunk_holder_it;
        }

        pointer operator->() const {
            return *m_chunk_holder_it;
        }

        operator IteratorBase<const_chunk_holder_iterator>() const {
            return IteratorBase<const_chunk_holder_iterator>(m_chunk_holder_it);
        }
    };
public:
    using iterator = IteratorBase<chunk_holder_iterator>;
    using const_iterator = IteratorBase<const_chunk_holder_iterator>;

    void freeHolders(chunk_holder_iterator first, chunk_holder_iterator last) {
        for_each(first, last, [](ChunkHolder chunk_holder) {
                    delete chunk_holder;
                });
    }


public:

    ArrayOfChunks() = default;
    ArrayOfChunks(size_t no_chunks): m_chunk_holders(no_chunks) {
        chunk_holder_iterator it = m_chunk_holders.begin();
        try {
            for (; it != m_chunk_holders.end(); ++it) {
                *it = new Chunk;
            }
        } catch(...) {
            freeHolders(m_chunk_holders.begin(), it);
            throw;
        }
    }

    ArrayOfChunks(const ArrayOfChunks& that): ArrayOfChunks(that.size()) {
        chunk_holder_iterator this_holder_it = m_chunk_holders.begin();
        try {
            std::for_each(that.cbegin(), that.cend(), [&this_holder_it](const Chunk& that_chunk) {
                  ChunkHolder& this_holder = *this_holder_it;
                  *this_holder = that_chunk;
                  ++this_holder_it;
                    });
        } catch(...) {
            freeHolders(m_chunk_holders.begin(), this_holder_it);
            throw;
        }
    }

    ArrayOfChunks& operator=(const ArrayOfChunks& that) {
        // TODO: better implementation
        ArrayOfChunks tmp = that;
        swap(tmp);
        return *this;
    }

    void swap(ArrayOfChunks& that) noexcept {
        m_chunk_holders.swap(that.m_chunk_holders);
    }

    iterator begin() {
        return iterator(m_chunk_holders.begin());
    }

    iterator end() {
        return iterator(m_chunk_holders.end());
    }

    const_iterator begin() const {
        return const_iterator(m_chunk_holders.cbegin());
    }

    const_iterator end() const {
        return const_iterator(m_chunk_holders.cend());
    }

    const_iterator cbegin() const {
        return begin();
    }

    const_iterator cend() const {
        return end();
    }

    Chunk& operator[](size_t pos) {
        return *m_chunk_holders[pos];
    }

    const char& operator[](size_t pos) const {
        return *m_chunk_holders[pos];
    }

    size_t size() const noexcept {
        return m_chunk_holders.size();
    }

    void extendBack() {
        m_chunk_holders.addHolderAtBack();
        m_chunk_holders.back() = new Chunk;
    }

    void extendFront() {
        m_chunk_holders.addHolderAtFront();
        m_chunk_holders.front() = new Chunk;
    }

    ~ArrayOfChunks() {
        freeFirstNHolders(m_chunk_holders.size());
    }
};


template<typename T>
class Deque {
private:
    static constexpr size_t chunk_sz = 64;
    static constexpr size_t bytes_in_chunk = chunk_sz * sizeof(T);

    using ArrayOfChunksT = ArrayOfChunks<bytes_in_chunk>;

    template<typename U, typename ChunkIteratorT>
    class IteratorBase {
    public:
        using iterator_category = std::random_access_iterator_tag;
        using value_type = U;
        using difference_type = std::ptrdiff_t;
        using reference = value_type&;
        using pointer = value_type*;

    private:
        ChunkIteratorT m_chunk_it;
        pointer m_item_ptr;

        pointer getPointerByPosition(size_t pos_in_chunk) const {
            return reinterpret_cast<pointer>(m_chunk_it->data()) + pos_in_chunk;
        }

        pointer getBlockBegin() const {
            return getPointerByPosition(0);
        }

        pointer getBlockEnd() const {
            return getPointerByPosition(chunk_sz);
        }

        size_t getPositionInChunk() const {
            return static_cast<size_t>(m_item_ptr - getBlockBegin());
        }

    public:
        IteratorBase(ChunkIteratorT chunk_it, size_t pos_in_chunk)
            : m_chunk_it(chunk_it), m_item_ptr(getPointerByPosition(pos_in_chunk)) {}

        IteratorBase& operator++() {
            ++m_item_ptr;
            if (m_item_ptr == getBlockEnd()) {
                ++m_chunk_it;
                m_item_ptr = getBlockBegin();
            }
            return *this;
        }

        IteratorBase operator++(int) {
            IteratorBase result = *this;
            ++(*this);
            return result;
        }

        IteratorBase& operator--() {
            if (m_item_ptr == getBlockBegin()) {
                --m_chunk_it;
                m_item_ptr = getBlockEnd();
            }
            --m_item_ptr;
            return *this;
        }

        IteratorBase operator--(int) {
            IteratorBase result = *this;
            --(*this);
            return result;
        }

        auto operator<=>(const IteratorBase&) const = default;

        difference_type operator-(IteratorBase that) const {
            return static_cast<difference_type>(chunk_sz) * (m_chunk_it - that.m_chunk_it)
                + static_cast<difference_type>(getPositionInChunk()) - static_cast<difference_type>(that.getPositionInChunk());
        }

        IteratorBase& operator+=(difference_type n) {
            size_t chunk_shift = static_cast<size_t>(std::abs(n)) / chunk_sz;
            size_t pos_in_chunk_shift = static_cast<size_t>(std::abs(n)) % chunk_sz;
            size_t final_pos = getPositionInChunk();
            if (n >= 0) {
                m_chunk_it += static_cast<typename ChunkIteratorT::difference_type>(chunk_shift);
                final_pos += pos_in_chunk_shift;
                if (final_pos >= chunk_sz) {
                    ++m_chunk_it;
                    final_pos -= chunk_sz;
                }
            } else {
                m_chunk_it -= static_cast<typename ChunkIteratorT::difference_type>(chunk_shift);
                if (final_pos < pos_in_chunk_shift) {
                    --m_chunk_it;
                    final_pos += chunk_sz;
                }
                final_pos -= pos_in_chunk_shift;
            }
            m_item_ptr = getPointerByPosition(final_pos);
            return *this;
        }

        IteratorBase operator+(difference_type n) const {
            IteratorBase result = *this;
            result += n;
            return result;
        }

        IteratorBase& operator-=(difference_type n) {
            return operator+=(-n);
        }

        IteratorBase operator-(difference_type n) const {
            return operator+(-n);
        }

        reference operator*() const {
            return *m_item_ptr;
        }

        pointer operator->() const {
            return &operator*();
        }

        operator IteratorBase<const U, typename ArrayOfChunksT::const_iterator>() const {
            return IteratorBase<const U, typename ArrayOfChunksT::const_iterator>(m_chunk_it, getPositionInChunk());
        }
    };

public:
    using iterator = IteratorBase<T, typename ArrayOfChunksT::iterator>;
    using const_iterator = IteratorBase<const T, typename ArrayOfChunksT::const_iterator>;
    using reverse_iterator = std::reverse_iterator<iterator>;
    using const_reverse_iterator = std::reverse_iterator<const_iterator>;

private:
    iterator constructIteratorFromOffset(size_t offset) {
        size_t chunk_i = offset / chunk_sz;
        size_t pos_in_chunk = offset % chunk_sz;
        return iterator(m_chunks.begin() + static_cast<typename ArrayOfChunksT::iterator::difference_type>(chunk_i), pos_in_chunk);
    }

    iterator constructIteratorFromPosition(size_t position) {
        return constructIteratorFromOffset(m_begin_offset + position);
    }

    size_t getPositionByIterator(const_iterator it) const {
        return static_cast<size_t>(it - begin());
    }

    // Invariant: there is always space for one T object at the beginning and at the end
    ArrayOfChunks<bytes_in_chunk> m_chunks;
    size_t m_begin_offset{};
    size_t m_end_offset{};

    void reserveSpace() {
        if (m_end_offset == m_chunks.size() * chunk_sz) {
            m_chunks.extendBack();
        }
        if (m_begin_offset == 0) {
            m_chunks.extendFront();
            m_begin_offset += chunk_sz;
            m_end_offset += chunk_sz;
        }
    }

    void construct(iterator it, const T& value) {
        T* ptr = &(*it);
        new (ptr) T(value);
    }

    void destroy(iterator it) {
        it->~T();
    }

    static size_t calculateRequiredNumberOfChunks(size_t no_objects) {
        return (no_objects + chunk_sz - 1) / chunk_sz;
    }

    void destroyRange(iterator first, iterator last) {
        for (iterator it = first; it != last; ++it) {
            destroy(it);
        }
    }

    template<typename InputIt>
    void constructRange(iterator first, iterator last, InputIt input_it) {
        iterator it = first;
        try {
            for (; it != last; ++it) {
                construct(it, *input_it++);
            }
        } catch(...) {
            destroyRange(first, it);
            throw;
        }
    }

public:
    using value_type = T;
    using reference = value_type&;
    using const_reference = const value_type&;
    using difference_type = typename iterator::difference_type;
    using size_type = size_t;

    Deque(): m_chunks(1), m_begin_offset(1), m_end_offset(1) {
        assert(m_chunks.size() >= 1);
    }

    Deque(size_t n, const T& value)
        : m_chunks(calculateRequiredNumberOfChunks(n + 2)) // + 2 in order to follow the Invariant
        , m_begin_offset(1)
        , m_end_offset(n + 1) {
        constructRange(begin(), end(), makeYieldIterator(value));
    }

    Deque(size_t n): Deque(n, T()) {}

    Deque(const Deque& that)
        : m_chunks(that.m_chunks)
        , m_begin_offset(that.m_begin_offset)
        , m_end_offset(that.m_end_offset) {
        constructRange(begin(), end(), that.cbegin());
    }

    Deque& operator=(const Deque& that) {
        Deque tmp = that;
        swap(tmp);
        return *this;
    }

    ~Deque() {
        destroyRange(begin(), end());
    }

    void swap(Deque& that) {
        m_chunks.swap(that.m_chunks);
        std::swap(m_begin_offset, that.m_begin_offset);
        std::swap(m_end_offset, that.m_end_offset);
    }

    iterator begin() noexcept {
        return constructIteratorFromOffset(m_begin_offset);
    }

    iterator end() noexcept {
        return constructIteratorFromOffset(m_end_offset); // m_end_offset is always less then capacity due to magic Invariant
    }

private:
    Deque<T>* removeConstness() const {
        return const_cast<Deque<T>*>(this);
    }

public:

    const_iterator begin() const noexcept {
        return removeConstness()->begin();
    }

    const_iterator end() const noexcept {
        return removeConstness()->end();
    }

    const_iterator cbegin() const noexcept {
        return begin();
    }

    const_iterator cend() const noexcept {
        return end();
    }

    reverse_iterator rbegin() noexcept {
        return reverse_iterator(end());
    }

    reverse_iterator rend() noexcept {
        return reverse_iterator(begin());
    }

    const_reverse_iterator rbegin() const noexcept {
        return const_reverse_iterator(end());
    }

    const_reverse_iterator rend() const noexcept {
        return const_reverse_iterator(begin());
    }

    const_reverse_iterator crbegin() const noexcept {
        return const_reverse_iterator(end());
    }

    const_reverse_iterator crend() const noexcept {
        return const_reverse_iterator(begin());
    }

    size_t size() const noexcept {
        return m_end_offset - m_begin_offset;
    }

    bool empty() const {
        return size() == 0;
    }

    T& operator[](size_t pos) noexcept {
        return *(begin() += static_cast<typename iterator::difference_type>(pos));
    }

    const T& operator[](size_t pos) const {
        return removeConstness()->operator[](pos);
    }

    T& at( size_t pos) {
        if (pos >= size()) {
            throw std::out_of_range("Out of range in Deque<T>::at");
        }
        return operator[](pos);
    }

    const T& at( size_t pos) const {
        return removeConstness()->at(pos);
    }

    T& front() {
        return *begin();
    }

    T& back() {
        return *rbegin();
    }

    const T& front() const {
        return removeConstness()->front();
    }

    const T& back() const {
        return removeConstness()->back();
    }

    void push_back(const T& value) {
        construct(end(), value); // correct because of magic Invariant
        ++m_end_offset;
        try {
            reserveSpace();
        } catch(...) {
            pop_back();
        }
    }

    void push_front(const T& value) {
        construct(--begin(), value); // correct decrement because of our magic Invariant
        --m_begin_offset;
        try {
            reserveSpace();
        } catch(...) {
            pop_front();
        }
    }

    void pop_back() {
        erase(std::prev(end()));
    }

    void pop_front() {
        erase(begin());
    }

    iterator insert(iterator it, const T& value) {
        if (it == begin()) {
            push_front(value);
            return begin();
        }
        const size_t position = getPositionByIterator(it);
        push_back(value);
        iterator resulting_it = constructIteratorFromPosition(position);
        for (iterator it_tmp = end(); --it_tmp != resulting_it; ) {
            std::swap(*std::prev(it_tmp), *it_tmp);
        }
        return resulting_it;
    }

    iterator erase(iterator it) {
        size_t position = getPositionByIterator(it);
        if (it == begin() || it == std::prev(end())) {
            destroy(it);
            if (it == begin()) {
                ++m_begin_offset;
            } else {
                --m_end_offset;
            }
        } else {
            for (iterator it_tmp = it; std::next(it_tmp) != end(); ++it_tmp) {
                *it_tmp = *std::next(it_tmp);
            }
            pop_back();
        }
        return constructIteratorFromPosition(position);
    }
};

