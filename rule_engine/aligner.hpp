#pragma once
#include <string>
#include <vector>
#include <algorithm>

using namespace std;
#include "common.hpp"
#include "MyArrays.hpp"

NAMED_PAIR(VarConstraint, int, index, int, value);
NAMED_PAIR(VarOccurence, int, sentence, int, index);

struct AlignmentVarInfo {
    LimitedArray<VarOccurence, MAX_DOMAIN_VARS> occurences;
    // one occurence per sentence
    LimitedArray<VarOccurence, MAX_DOMAIN_VARS> key_occurences;
    LimitedArray<int, MAX_DOMAIN_VARS> different_than;
    LimitedArray<int, MAX_DOMAIN_VARS> different_than_const;
};


struct Domain;
struct AlignmentInfo {
    Domain *destination_theorem, *destination_sentence;
    int sources_new_valuations_n;
    LimitedArray<Domain*, MAX_SENTENCES_IN_THEOREM> source_sentences;
    LimitedArray<LimitedArray<VarConstraint, MAX_DOMAIN_VARS>, MAX_SENTENCES_IN_THEOREM>
        source_constraints;
    LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> var_infos;
    LimitedArray<int, MAX_DOMAIN_VARS> binding_order;

    // filling_pattern - negative = (-(renamed_token + 1)), positive = exp_var_id + 1
    LimitedArray<int, MAX_DOMAIN_VARS> domain_filling_pattern;
    // one var occurence per sentence
    LimitedArray<VarOccurence, MAX_SENTENCES_IN_THEOREM> key_occurences; 
    LimitedArray<LimitedArray<int, MAX_DOMAIN_VARS>, MAX_SENTENCES_IN_THEOREM> var_equivalence;
};


void fix_point_align(vector<AlignmentInfo> &to_align);

namespace DTYPE {
    enum {
        SENTENCE,
        THEOREM
    };
};

struct Domain {
    size_t id; // hash of the pattern
    int type; // 
    string pattern; // next and init are replaced by true, legal by does
    string original_pattern; // pattern 
    vector<DomainValuation> valuations;
    int valuation_size;
    Domain(){}
    Domain(string _pattern, string _original_pattern, int _type) {
        type = _type;
        pattern = _pattern;
        original_pattern = _original_pattern;
        id = str_hasher(pattern);
        valuation_size = count(pattern.begin(), pattern.end(), '#');
        assert(valuation_size <= MAX_DOMAIN_VARS);
    }
    
    string to_string() {
        string res = pattern + "\n";
        for (auto &dv: valuations) {
            for (int i = 0; i < valuation_size; ++i) {
                res += " " + globals().reverse_numeric_rename[dv[i]];
            }
            res += "\n";
        }
        return res;
    }
    
    string to_full_string() const {
        string res;
        for (const auto &valuation: valuations) {
            res += to_string_with_valuation(valuation) + '\n';
        }
        return res;
    }

    string to_string_with_valuation(const DomainValuation &valuation) const {
        string res;
        int i = 0;
        for (char c: original_pattern) {
            string to_append;
            if (c == '#') {
                to_append = globals().reverse_numeric_rename[valuation[i]];
                ++i;
            } else {
                to_append = c;
            }
            res += to_append;
        }
        return res;
    }
};

struct _Aligner {
    typedef LimitedArray<pair<int, int>, MAX_SENTENCES_IN_THEOREM> IndexBound;
    typedef LimitedArray<const vector<DomainValuation>*, MAX_SENTENCES_IN_THEOREM> SourcesValuations;
    LimitedArray<IndexBound, MAX_TERMS_N * 3> bounds_stack;
    LimitedArray<int, MAX_TERMS_N * 3> indices_memory_bank;

    const AlignmentInfo *ai;
    SourcesValuations sources_valuations;

    LimitedArray<SizedArray<int>, MAX_SENTENCES_IN_THEOREM> indices;
    LimitedArray<LimitedArray<int, MAX_DOMAIN_VARS>, MAX_DOMAIN_VARS> banned_var_values;
    vector<DomainValuation> new_valuations;

    void find_valuations(const AlignmentInfo *_ai) {
        initialize(_ai);
        compute();
    }

    void initialize(const AlignmentInfo *_ai) {
        ai = _ai;
        new_valuations.resize(0);
        bounds_stack.resize(0);
        indices_memory_bank.resize(0);
        sources_valuations.resize(0);
        for (const auto &source: ai->source_sentences) {
            sources_valuations.append(&source->valuations);
        }
    }

    int sentences_n() const {
        return ai->source_sentences.size;
    }

    int vars_n() const {
        return ai->var_infos.size;
    }

    bool prepare_indices();
    void split_by_var(int split_by_var_id);
    void initialize_banned_var_values();
    void ban_by_var(int var_id); 
    void unban(int var_id);
    void const_only_filler();
    void compute();

    void print_bounds_stack();
};
