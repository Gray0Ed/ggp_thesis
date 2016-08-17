#pragma once
#include <cassert>

template <typename T>
struct SizedArray {
    T *items;
    size_t size;
    typedef T* Iterator;
    typedef const T* ConstIterator;

    void set_items(T *_items, size_t _size) {
        items = _items;
        size = _size;
    }

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

    SizedArray() {
        size = 0;
        items = 0;
    }

    SizedArray(const SizedArray<T> &la) {
        assert(size >= la.size);
        size = la.size;
        for (size_t i = 0; i < size; ++i) items[i] = la.items[i];
    }

    SizedArray<T> &operator=(const SizedArray<T> &la) {
        assert(size >= la.size);
        size = la.size;
        for (size_t i = 0; i < size; ++i) items[i] = la.items[i];
        return *this;
    }

    bool operator==(const SizedArray<T> &la) const {
        if (la.size != size) return false;

        for (size_t i = 0; i < size; ++i) {
            if (la[i] != items[i]) return false;
        }
        return true;
    }

    bool operator<(const SizedArray<T> &la) const {
        size_t mins = size;
        if (la.size < size) mins = la.size;
        for (size_t i = 0; i < mins; ++i) {
            if (items[i] < la[i]) return true;
            if (items[i] > la[i]) return false;
        }
        if (la.size == size) return false;
        return size < la.size;
    }

    T &operator[](size_t i) {
        assert(size >= 0);
        assert(i < size && i >= 0);
        return items[i];
    }

    T operator[](size_t i) const {
        assert(size >= 0);
        assert(i < size && i >= 0);
        return items[i];
    }

    T &back() {
        return back(0);
    }

    T &back() const {
        return back(0);
    }

    T &back(size_t i) {
        assert(i < size);
        return (*this)[size - 1 - i];
    }

    T &back(size_t i) const {
        assert(i < size);
        return (*this)[size - 1 - i];
    }

    bool contains(const T& value) const {
        for (size_t i = 0; i < size; ++i) {
            if (items[i] == value) return true;
        }
        return false;
    }
};

template <typename T, int MAX_SZ>
struct LimitedArray: public SizedArray<T> {
    T items[MAX_SZ + 1];

    LimitedArray() {
        set_items(items, 0);
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

    LimitedArray(const LimitedArray<T, MAX_SZ> &la) {
        size = la.size;
        for (size_t i = 0; i < size; ++i) items[i] = la.items[i];
    }

    LimitedArray<T, MAX_SZ> &operator=(const LimitedArray<T, MAX_SZ> &la) {
        assert(size >= la.size);
        size = la.size;
        for (size_t i = 0; i < size; ++i) items[i] = la.items[i];
        return *this;
    }
};
