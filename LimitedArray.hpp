#include <cassert>
template <typename T, int MAX_SZ>
struct LimitedArray {
    T items[MAX_SZ];
    size_t size;
    typedef T* Iterator;
    typedef const T* ConstIterator;

    Iterator begin() {
        return items + 0;
    }

    Iterator end() {
        return items + size;
    }

    ConstIterator begin() const {
        return items + 0;
    }

    ConstIterator end() const {
        return items + size;
    }

    LimitedArray() {
        size = 0;
    }

    LimitedArray(const LimitedArray<T, MAX_SZ> &la) {
        size = la.size;
        for (int i = 0; i < size; ++i) items[i] = la.items[i];
    }

    LimitedArray<T, MAX_SZ> &operator=(const LimitedArray<T, MAX_SZ> &la) {
        size = la.size;
        for (int i = 0; i < size; ++i) items[i] = la.items[i];
        return *this;
    }

    bool operator==(const LimitedArray<T, MAX_SZ> &la) const {
        if (la.size != size) return false;

        for (int i = 0; i < size; ++i) {
            if (la[i] != items[i]) return false;
        }
        return true;
    }

    bool operator<(const LimitedArray<T, MAX_SZ> &la) const {
        int mins = size;
        if (la.size < size) mins = la.size;
        for (int i = 0; i < mins; ++i) {
            if (items[i] < la[i]) return true;
            if (items[i] > la[i]) return false;
        }
        if (la.size == size) return false;
        return size < la.size;
    }

    T &operator[](int i) {
        assert(size >= 0);
        assert(size <= MAX_SZ);
        assert(i < size && i >= 0);
        return items[i];
    }

    T operator[](int i) const {
        assert(size >= 0);
        assert(size <= MAX_SZ);
        assert(i < size && i >= 0);
        return items[i];
    }

    void resize(size_t new_size) {
        assert(new_size <= MAX_SZ);
        size = new_size;
    }

    void grow() {
        resize(size + 1);
    }

    void pop() {
        assert(size > 0);
        resize(size - 1);
    }

    void append(const T& t) {
        assert(size < MAX_SZ);
        items[size++] = t;
    }

    T &back() {
        return back(0);
    }

    T &back() const {
        return back(0);
    }

    T &back(int i) {
        return (*this)[size - 1 - i];
    }

    T &back(int i) const {
        return (*this)[size - 1 - i];
    }

    bool contains(const T& value) const {
        for (int i = 0; i < size; ++i) {
            if (items[i] == value) return true;
        }
        return false;
    }
};
