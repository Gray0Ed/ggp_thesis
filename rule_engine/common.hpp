#pragma once
#include "MyArrays.hpp"
#include <unordered_map>
#include <vector>
using namespace std;

const int MAX_DOMAIN_VARS = 80;
const int MAX_SENTENCES_IN_THEOREM = 15;
const int MAX_TERMS_N = 10000;
typedef LimitedArray<short, MAX_DOMAIN_VARS> DomainValuation;


#define NAMED_PAIR(name, first_v_type, first_v_name, second_v_type, second_v_name) \
    struct name {\
        first_v_type first_v_name;\
        second_v_type second_v_name;\
        name(){}\
        name(first_v_type a, second_v_type b) {\
            this->first_v_name = a;\
            this->second_v_name = b;\
        }\
        bool operator==(const name &_cmpw) const {\
            return first_v_name == _cmpw.first_v_name && second_v_name == _cmpw.second_v_name;\
        }\
    }


inline size_t str_hasher(const string &s) {
    static hash<string> hasher;
    return hasher(s);
}

struct Globals {
    unordered_map<string, int> numeric_rename;
    vector<string> reverse_numeric_rename;
};

inline Globals &globals() {
    static Globals g;
    return g;
}
