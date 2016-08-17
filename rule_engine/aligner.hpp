#include <string>
#include <vector>

using namespace std;
#include "common.hpp"
#include "MyArray.hpp"

NAMED_PAIR(VarConstraint, int, index, int, value);
NAMED_PAIR(VarOccurence, int, sentence, int, index);

void fix_point_align(const vector<AlignmentInfo> &to_align);

namespace DTYPE {
    enum {
        SENTENCE,
        THEOREM
    };
};

struct Domain {
    size_t id; // hash of the pattern
    int type; // 
    string pattern;
    vector<DomainValuation> valuations;
    int valuation_size;
    Domain(){}
    Domain(string _pattern, int _type) {
        type = _type;
        pattern = _pattern;
        id = str_hasher(pattern);
        valuation_size = count(pattern.begin(), pattern.end(), '#');
        assert(valuation_size <= MAX_DOMAIN_VARS);
    }
    
    string to_string() {
        string res = pattern + "\n";
        for (auto &dv: valuations) {
            for (int i = 0; i < valuation_size; ++i) {
                res += " " + reverse_numeric_rename[dv[i]];
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
        for (char c: pattern) {
            string to_append;
            if (c == '#') {
                to_append = reverse_numeric_rename[valuation[i]];
                ++i;
            } else {
                to_append = c;
            }
            res += to_append;
        }
        return res;
    }
};

struct AlignmentVarInfo {
    LimitedArray<VarOccurence, MAX_DOMAIN_VARS> occurences;
    LimitedArray<int, MAX_DOMAIN_VARS> different_than;
    LimitedArray<int, MAX_DOMAIN_VARS> different_than_const;
};

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
};


struct _Aligner {
    typedef LimitedArray<pair<int, int>, MAX_SENTENCES_IN_THEOREM> IndexBound;
    typedef LimitedArray<const vector<DomainValuation>*, MAX_SENTENCES_IN_THEOREM> SourcesValuations;
    LimitedArray<IndexBound, MAX_TERMS_N * 3> bounds_stack;
    LimitedArray<int, MAX_TERMS_N * 3> indices_memory_bank;

    const AlignerInfo *ai;
    SourcesValuations sources_valuations;

    LimitedArray<SizedArray<int>, MAX_SENTENCES_IN_THEOREM> indices;
    LimitedArray<LimitedArray<int, MAX_DOMAIN_VARS>, MAX_DOMAIN_VARS> banned_var_values;
    vector<DomainValuation> new_valuations;

    void fiind_valuations(const AlignerInfo *_ai) {
        initialize();
        compute();
    }

    void initialize(const AlignerInfo *_ai) {
        ai = _ai;
        new_valuations.resize(0);
        bounds_stack.resize(0);
        indices_memory_bank.resize(0);
        sources_valuations.resize(0);
        for (const auto &source: ai->source_sentence) {
            sources_valuations.append(source);
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
};
