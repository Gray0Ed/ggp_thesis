#pragma once
#include <vector>
#include <string>
#include <unordered_set>
#include <unordered_map>
using namespace std;
#include "common.hpp"
#include "aligner.hpp"
#include "GDLTokenizer.hpp"

namespace TYPE {
    enum {
        NONE,
        VAR,
        CONST,
        THEOREM,
        SENTENCE,
        TUPLE,
    };
};

int str_token_to_int(const string &token);


struct HighNode {
    int type;
    size_t theorem_vars_n;
    size_t domain_hash;
    string domain_pattern;
    int value;
    int exp_var_id;
    bool contains_variable;
    GDLToken debug_token;
    vector<HighNode> sub;
    int max_sub_size, max_theorem_vars_n;

    static vector<HighNode> generate_from_tokens(const vector<GDLToken> &tokens);

    HighNode() {
        reset();
    }

    void reset() {
        max_sub_size = 0;
        max_theorem_vars_n = 0;
        theorem_vars_n = 0;
        sub.resize(0);
        value = -1;
        exp_var_id = -1;
    }

    string to_string() const;
    void fill_from_token(const GDLToken &t, 
            unordered_map<int, int> &var_mapping,
            int induced_type=TYPE::NONE);
    void fill_from_token(const GDLToken &t);
    pair<string, string> assign_domain_hash_and_pattern(
            unordered_map<size_t, unordered_set<string>> & checker);
    void gather_base_valuations_from_consts(DomainValuation &to_fill) const;
    void collect_distinct_info(LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos) const;
    void fill_var_constraints(LimitedArray<VarConstraint, MAX_DOMAIN_VARS> &constraints) const;
    void fill_var_constraints(
            LimitedArray<VarConstraint, MAX_DOMAIN_VARS> &constraints,
            int &index) const;
    void fill_var_occurences(
            LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos, 
            int sentence_index) const;
    void fill_var_occurences(
            LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos, 
            int sentence_index,
            int &var_index) const;
    void fill_var_in_dom_indices(LimitedArray<int, MAX_DOMAIN_VARS> &to_fill) const;
    void fill_key_occurences(AlignmentVarInfo &var_info) const;
    void fill_var_equivalence(AlignmentInfo &ai) const;
    AlignmentInfo alignment_info() const;
};
