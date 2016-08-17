#include <iostream>
#include <fstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cctype>
#include <cassert>
#include <functional>
#include <algorithm>
#include <cstring>
#include <climits>
#include <tuple>


#ifndef NO_BACKWARD
#define BACKWARD_HAS_DW 1
#include "backward.hpp"

namespace backward {
    backward::SignalHandling sh;
};

#endif

#include "LimitedArray.hpp"
#include "GDLTokenizer.hpp"
using namespace std;

const int MAX_DOMAIN_VARS = 80;
const int MAX_SENTENCES_IN_THEOREM = 15;
const int MAX_TERMS_N = 100000;

hash<string> str_hasher;
typedef LimitedArray<short, MAX_DOMAIN_VARS> DomainValuation;

unordered_map<string, int> numeric_rename;
vector<string> reverse_numeric_rename;

void replace_first_occurence(string &to_modify, const string &to_replace,
                             const string &replacement) {
    auto pos = to_modify.find(to_replace);
    if (pos != string::npos) {
        to_modify.replace(pos, to_replace.size(), replacement);
    }
}

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
unordered_map<size_t, Domain> domain_map;

#define NAMED_PAIR(name, first_v_type, first_v_name, second_v_type, second_v_name) \
    struct name {\
        first_v_type first_v_name;\
        second_v_type second_v_name;\
        name(){}\
        name(first_v_type a, second_v_type b) {\
            this->first_v_name = a;\
            this->second_v_name = b;\
        }\
    }
NAMED_PAIR(VarConstraint, int, index, int, value);
NAMED_PAIR(VarOccurence, int, sentence, int, index);

struct AlignmentVarInfo {
    LimitedArray<VarOccurence, MAX_DOMAIN_VARS> occurences;
    LimitedArray<int, MAX_DOMAIN_VARS> different_than;
    LimitedArray<int, MAX_DOMAIN_VARS> different_than_const;
};

struct AlignmentInfo {
    size_t destination_theorem, destination_sentence;
    int sources_new_valuations_n;
    LimitedArray<size_t, MAX_SENTENCES_IN_THEOREM> source_sentences;
    LimitedArray<LimitedArray<VarConstraint, MAX_DOMAIN_VARS>, MAX_SENTENCES_IN_THEOREM>
        source_constraints;
    LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> var_infos;
    LimitedArray<int, MAX_DOMAIN_VARS> binding_order;

    // filling_pattern - negative = (-(renamed_token + 1)), positive = exp_var_id + 1
    LimitedArray<int, MAX_DOMAIN_VARS> domain_filling_pattern;
};

int rename(const string &token) {
    if (numeric_rename.count(token) == 0) {
        size_t s = numeric_rename.size();
        numeric_rename[token] = s;
        reverse_numeric_rename.push_back(token);
        assert(reverse_numeric_rename.size() == s + 1);
        assert(s <= SHRT_MAX);
    }
    return numeric_rename[token];
}

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

    string to_string() const {
        string res = "(";
        if (type == TYPE::THEOREM) {
            res += " <=";
        }
        if (type == TYPE::SENTENCE || type == TYPE::TUPLE) {
            res += " " + reverse_numeric_rename[value];
        }
        for (const auto &node: sub) {
            if (node.type == TYPE::VAR || node.type == TYPE::CONST) {
                res += " " + reverse_numeric_rename[node.value];
            } else if (node.type == TYPE::SENTENCE || node.type == TYPE::TUPLE) {
                res += " " + node.to_string();
            } else {
                assert(0);
            }
        }
        assert(type == TYPE::THEOREM || type == TYPE::SENTENCE || type == TYPE::TUPLE);
        res += " )";
        return res;
    }

    void fill_from_token(const GDLToken &t, 
            unordered_map<int, int> &var_mapping,
            int induced_type=TYPE::NONE) {
        debug_token = t;
        contains_variable = false;
        if (t.leaf()) {
            assert(!t.val.empty());
            int renamed = rename(t.val);
            if (induced_type == TYPE::TUPLE) {
                if (t.val[0] == '?') {
                    type = TYPE::VAR;
                    if (var_mapping.count(renamed) == 0) {
                        int sz = var_mapping.size();
                        var_mapping[renamed] = sz; 
                    }
                    exp_var_id = var_mapping[renamed];
                    contains_variable = true;
                } else {
                    type = TYPE::CONST;
                    value = renamed;
                }
            } else {
                assert(induced_type == TYPE::SENTENCE);
                assert(t.val[0] != '?');
                type = TYPE::SENTENCE;
                value = renamed;
            }
        } else if (t(0) == "<=") {
            assert(t.sub.size() >= 3);
            assert(induced_type == TYPE::NONE);
            type = TYPE::THEOREM;
            sub.resize(t.sub.size() - 1);
            for (size_t i = 1; i < t.sub.size(); ++i) {
                sub[i - 1].fill_from_token(t.sub[i], var_mapping, TYPE::SENTENCE);
                contains_variable = contains_variable || sub[i - 1].contains_variable;
            }
            theorem_vars_n = var_mapping.size();
        } else {
            if (induced_type == TYPE::TUPLE) {
                type = TYPE::TUPLE;
            } else {
                assert(induced_type == TYPE::SENTENCE || induced_type == TYPE::NONE);
                type = TYPE::SENTENCE;
            }
            assert(!t.sub.empty());
            assert(t(0) != "");
            assert(t.sub[0].leaf());
            value = rename(t(0));
            sub.resize(t.sub.size() - 1);
            for (size_t i = 1; i < t.sub.size(); ++i) {
                sub[i - 1].fill_from_token(t.sub[i], var_mapping, TYPE::TUPLE);
                contains_variable = contains_variable || sub[i - 1].contains_variable;
            }
        }
        assert(type != TYPE::NONE);
    }

    static vector<HighNode> generate_from_tokens(const vector<GDLToken> &tokens) {
        vector<HighNode> res;
        res.reserve(tokens.size());
        for (auto &tok: tokens) {
            unordered_map<int, int> var_mapping;
            res.push_back(HighNode());
            res.back().fill_from_token(tok, var_mapping);
        }
        return res;
    }

    string assign_domain_hash_and_pattern(unordered_map<size_t, unordered_set<string>> & checker) {
        string res;
        if (type != TYPE::THEOREM) {
            res = reverse_numeric_rename[value];
        }
        if (res == "next" || res == "init") {
            res = "true";
        }
        if (res == "legal") {
            res = "does";
        }
        if (type == TYPE::THEOREM) {
            res = "( <=" + res;
        }
        bool first_done = false;
        for (HighNode &hn: sub) {
            if (hn.type == TYPE::VAR || hn.type == TYPE::CONST) {
                res += " #";
            } else if (hn.type == TYPE::SENTENCE || hn.type == TYPE::TUPLE) {
                res += " ( " + hn.assign_domain_hash_and_pattern(checker) + " )";
            } else {
                cerr << debug_token.to_string() << endl;
                cerr << hn.type << " " << hn.debug_token.to_string() << endl;
                assert(0);
            }
            if (type == TYPE::THEOREM && !first_done) {
                first_done = true;
                assert(hn.type == TYPE::SENTENCE);
                replace_first_occurence(res, "true", "next");
                replace_first_occurence(res, "does", "legal");
            }
        }
        if (type == TYPE::THEOREM) {
            res += " )";
        }
        assert(type == TYPE::THEOREM || type == TYPE::SENTENCE || type == TYPE::TUPLE);
        if (type != TYPE::TUPLE) {
            domain_pattern = res;
            domain_hash = str_hasher(res);
            int domain_type;
            if (type == TYPE::THEOREM) {
                domain_type = DTYPE::THEOREM;
            } else {
                domain_type = DTYPE::SENTENCE;
            }
            domain_map[domain_hash] = Domain(domain_pattern, domain_type);
            if (checker.count(domain_hash) == 0) {
                checker[domain_hash] = unordered_set<string>();
            }
            checker[domain_hash].insert(domain_pattern);
            assert(domain_map[domain_hash].id == domain_hash);
        }
        assert(type == TYPE::THEOREM || (res.find("next") == string::npos && 
               res.find("legal") == string::npos && res.find("init") == string::npos));
        return res;
    }

    void gather_base_valuations_from_consts(DomainValuation &to_fill) const {
        for (const HighNode &hn: sub) {
            assert(hn.type == TYPE::CONST || hn.type == TYPE::TUPLE);
            if (hn.type == TYPE::CONST) {
                to_fill.append(hn.value);
            } else {
                hn.gather_base_valuations_from_consts(to_fill);
            }
        }
    }

    void collect_distinct_info(LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos) const {
        assert(reverse_numeric_rename[value] == "distinct");
        assert(sub.size() == 2);
        const HighNode *left_node = &sub[0];
        const HighNode *right_node = &sub[1];
        if (left_node->type == TYPE::CONST) {
            swap(left_node, right_node);
        }
        assert(left_node->type == TYPE::VAR);
        assert(right_node->type == TYPE::VAR || right_node->type == TYPE::CONST);
        if (right_node->type == TYPE::VAR) {
            var_infos[left_node->exp_var_id].different_than.append(right_node->exp_var_id);
            var_infos[right_node->exp_var_id].different_than.append(left_node->exp_var_id);
        } else {
            var_infos[left_node->exp_var_id].different_than_const.append(right_node->value);
        }
    }

    void fill_var_constraints(LimitedArray<VarConstraint, MAX_DOMAIN_VARS> &constraints) const {
        int index = 0;
        fill_var_constraints(constraints, index);
    }

    void fill_var_constraints(
            LimitedArray<VarConstraint, MAX_DOMAIN_VARS> &constraints,
            int &index) const {
        for (auto &node: sub) {
            if (node.type == TYPE::TUPLE) {
                node.fill_var_constraints(constraints, index);
            } else if (node.type == TYPE::CONST) {
                constraints.append(VarConstraint(index++, node.value));
            } else {
                assert(node.type == TYPE::VAR);
                ++index;
            }
        }
    }

    void fill_var_occurences(
            LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos, 
            int sentence_index) const {
        int var_index = 0;
        fill_var_occurences(var_infos, sentence_index, var_index);
    }

    void fill_var_occurences(
            LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos, 
            int sentence_index,
            int &var_index) const {
        for (auto &node: sub) {
            if (node.type == TYPE::VAR) {
                var_infos[node.exp_var_id].occurences.append(
                    VarOccurence(sentence_index, var_index++)
                );
            } else if (node.type == TYPE::CONST) {
                ++var_index;
            } else if (node.type == TYPE::TUPLE) {
                node.fill_var_occurences(var_infos, sentence_index, var_index);
            } else {
                assert(0);
            }
        }
    }

    void fill_var_in_dom_indices(LimitedArray<int, MAX_DOMAIN_VARS> &to_fill) const {
        for (auto &node: sub) {
            if (node.type == TYPE::VAR) {
                to_fill.append(node.exp_var_id + 1);
            } else if (node.type == TYPE::CONST) {
                to_fill.append(-(node.value + 1));
            } else if (node.type == TYPE::TUPLE || node.type == TYPE::SENTENCE) {
                node.fill_var_in_dom_indices(to_fill);
            } else {
                assert(0);
            }
        }
    }

    AlignmentInfo alignment_info() const {
        assert(type == TYPE::THEOREM);
        AlignmentInfo res;
        res.destination_theorem = domain_hash;
        res.destination_sentence = sub[0].domain_hash;
        res.sources_new_valuations_n = 1;
        res.var_infos.size = theorem_vars_n; 
        for (auto &vi: res.var_infos) {
            assert(vi.occurences.size == 0);
        }
        assert(res.domain_filling_pattern.size == 0);
        fill_var_in_dom_indices(res.domain_filling_pattern);
        auto &var_infos = res.var_infos;
        int counter = 0;
        for (size_t i = 1; i < sub.size(); ++i) {
            const string & sub_svalue = reverse_numeric_rename[sub[i].value];
            if (sub_svalue == "distinct") {
                sub[i].collect_distinct_info(var_infos);
            } else if (sub_svalue != "not") {
                res.source_sentences.append(sub[i].domain_hash);
                res.sources_new_valuations_n += domain_map[sub[i].domain_hash].valuations.size();
                res.source_constraints.grow();
                sub[i].fill_var_constraints(res.source_constraints.back());
                sub[i].fill_var_occurences(var_infos, counter);
                //cerr << sub[i].domain_pattern << " ";
                ++counter;
            }
        }

        res.binding_order.size = theorem_vars_n;
        for (size_t i = 0; i < theorem_vars_n; ++i) {
            res.binding_order[i] = i;
        }
        sort(res.binding_order.begin(), res.binding_order.end(),
            [&var_infos](const int &a, const int &b) -> bool {
                return var_infos[a].occurences.size > var_infos[b].occurences.size;
            }
        );
        return res;
    }
};

void collect_domain_types(vector<HighNode> & vhn) {
    unordered_map<size_t, unordered_set<string>> checker;
    for (HighNode &hn: vhn) {
        hn.assign_domain_hash_and_pattern(checker);
    }
    for (auto kv: checker) {
        assert(kv.second.size() < 2);
    }
}

void collect_initial_valuations(const vector<HighNode> &rules){
    for (const HighNode &hn: rules) {
        if (hn.type == TYPE::SENTENCE) {
            DomainValuation new_valuation;
            hn.gather_base_valuations_from_consts(new_valuation);
            domain_map[hn.domain_hash].valuations.push_back(new_valuation);
        }
    }
}

vector<AlignmentInfo> collect_alignment_infos(const vector<HighNode> &rules) {
    vector<AlignmentInfo> res;
    for (const auto &hn: rules) {
        if (hn.type == TYPE::THEOREM) {
            res.push_back(hn.alignment_info());
            //cerr << res.back().sources_new_valuations_n << endl;
            //cerr << hn.domain_pattern << endl;
            //cerr << domain_map[hn.sub[0].domain_hash].to_string();
        }
    }
    return res;
}

struct Aligner {
    const AlignmentInfo &ai;
    Aligner(const AlignmentInfo &_ai): ai(_ai) {}

    LimitedArray<vector<DomainValuation>*, MAX_SENTENCES_IN_THEOREM> valuations_sets;
    LimitedArray<LimitedArray<int, MAX_TERMS_N>, MAX_SENTENCES_IN_THEOREM> indices;
    LimitedArray<LimitedArray<int, MAX_DOMAIN_VARS>, MAX_DOMAIN_VARS> banned_var_values;
    vector<DomainValuation> new_valuations;

    typedef LimitedArray<pair<int, int>, MAX_SENTENCES_IN_THEOREM> IndexBound;
    LimitedArray<IndexBound, MAX_TERMS_N * 3> bounds_stack;

    int sentences_n() const {
        return ai.source_sentences.size;
    }

    int vars_n() const {
        return ai.var_infos.size;
    }

    bool prepare_indices() {
        for (int sentence_i = 0; sentence_i < sentences_n(); ++sentence_i) {
            valuations_sets[sentence_i] = &domain_map[ai.source_sentences[sentence_i]].valuations;
            int valuation_index = 0;
            for (const auto &valuation: (*valuations_sets[sentence_i])) {
                bool bad = false;
                for (const auto &var_constraint: ai.source_constraints[sentence_i]) {
                    if (valuation[var_constraint.index] != var_constraint.value) {
                        bad = true;
                        break;
                    }
                }
                if (!bad) {
                    indices[sentence_i].append(valuation_index);
                }
                ++valuation_index;
            }
            if (indices[sentence_i].size == 0) {
                return false;
            }
        }
        return true;
    }

    void split_by_var(int split_by_var_id) {
        const auto &occurences = ai.var_infos[split_by_var_id].occurences;
        const auto &banned_values = banned_var_values[split_by_var_id];
        const IndexBound input_bounds = bounds_stack.back();
        bounds_stack.pop();
        assert(occurences.size > 0);
        for (const auto &occurence: occurences) {
            const auto &bound = input_bounds[occurence.sentence];
            auto &sindices = indices[occurence.sentence];
            assert(sindices.size > 0);
            assert(bound.first < bound.second);
            auto &valuation_set = *valuations_sets[occurence.sentence];
            sort(&sindices[0] + bound.first, &sindices[0] + bound.second, 
                [&valuation_set, &occurence](const auto &a, const auto &b) -> bool {
                    return valuation_set[a][occurence.index] < valuation_set[b][occurence.index];
                }
            );
        }
        LimitedArray<int, MAX_SENTENCES_IN_THEOREM> processed_index;
        for (int i = 0; i < sentences_n(); ++i) {
            processed_index.append(input_bounds[i].first);
        }
        const auto &moccurence = occurences[0];
        const auto &mbound = input_bounds[moccurence.sentence];
        auto &mindices = indices[moccurence.sentence];
        auto &mvaluation_set = *valuations_sets[moccurence.sentence];
        auto &mindex = processed_index[moccurence.sentence];
        while (mindex < mbound.second) {
            const int value = 
                mvaluation_set[mindices[mindex]][moccurence.index];
            if (banned_values.contains(value)) {
                while (mindex < mbound.second && 
                        mvaluation_set[mindices[mindex]][moccurence.index] == value) {
                    ++mindex;
                }
                continue;
            }
            bool bad = false;
            bounds_stack.grow();
            IndexBound &ib_to_fill = bounds_stack.back();
            ib_to_fill.resize(sentences_n());
            for (auto &ib: ib_to_fill) {
                ib.first = -1;
                ib.second = -1;
            }
            for (const auto &occurence: occurences) {
                int &pi = processed_index[occurence.sentence];
                const auto &bound = input_bounds[occurence.sentence];
                assert(bound.first != bound.second);
                auto &sindices = indices[occurence.sentence];
                auto &valuation_set = *valuations_sets[occurence.sentence];
                while (pi < bound.second && valuation_set[sindices[pi]][occurence.index] < value) ++pi;
                auto sub_bound = make_pair(pi, pi);
                while (pi < bound.second && valuation_set[sindices[pi]][occurence.index] == value) ++pi;
                sub_bound.second = pi;
                if (sub_bound.second == sub_bound.first) {
                    bad = true;
                    break;
                }
                bounds_stack.back()[occurence.sentence] = sub_bound;
            }
            if (bad) {
                bounds_stack.pop();
            } else {
                for (int sentence_i = 0; sentence_i < sentences_n(); ++sentence_i) {
                    if (ib_to_fill[sentence_i].first == -1) {
                        ib_to_fill[sentence_i] = input_bounds[sentence_i];
                    }
                }
            }
        }
    }

    void initialize_banned_var_values() {
        for (const auto &vi: ai.var_infos) {
            banned_var_values.append(vi.different_than_const);
        }
    }

    void ban_by_var(int var_id) {
        const auto &oc = ai.var_infos[var_id].occurences[0];
        const auto &bound = bounds_stack.back()[oc.sentence];
        assert(bound.first < bound.second);
        const int value = valuations_sets[oc.sentence]->at(
                indices[oc.sentence][bound.first])[oc.index];
        for (int dvar_id: ai.var_infos[var_id].different_than) {
            banned_var_values[dvar_id].append(value);
        }
    }

    void unban(int var_id) {
        for (int dvar_id: ai.var_infos[var_id].different_than) {
            banned_var_values[dvar_id].pop();
        }
    }

    void const_only_filler() {
        DomainValuation new_valuation;
        for (int vi: ai.domain_filling_pattern) {
            assert(vi < 0);
            new_valuation.append(-vi - 1);
        }
        new_valuations.push_back(new_valuation);
    }

    void apply_new_valuations() {
        auto &dt = domain_map[ai.destination_theorem];
        auto &ds = domain_map[ai.destination_sentence];
        dt.valuations.insert(dt.valuations.end(), new_valuations.begin(), new_valuations.end());
        sort(dt.valuations.begin(), dt.valuations.end());
        auto dt_last = unique(dt.valuations.begin(), dt.valuations.end());
        dt.valuations.erase(dt_last, dt.valuations.end());

        for (auto & new_valuation: new_valuations) {
            new_valuation.resize(ds.valuation_size);
            ds.valuations.push_back(new_valuation);
        }
        sort(ds.valuations.begin(), ds.valuations.end());
        auto last = unique(ds.valuations.begin(), ds.valuations.end());
        ds.valuations.erase(last, ds.valuations.end());
    }

    void recompute() {
        if (sentences_n() == 0) {
            const_only_filler();
            apply_new_valuations();
            return;
        }
        indices.size = valuations_sets.size = sentences_n();
        if (!prepare_indices()) {
            return;
        }

        if (vars_n() == 0) {
            const_only_filler();
            apply_new_valuations();
            return;
        }
        initialize_banned_var_values();

        bounds_stack.resize(1);
        for (int i = 0; i < sentences_n(); ++i) {
            bounds_stack[0].append(make_pair(0, (int)indices[i].size));
        }
        split_by_var(ai.binding_order[0]);
        LimitedArray<int, MAX_DOMAIN_VARS> level_size;
        level_size.append(bounds_stack.size);
        //cerr << "boom" << endl;
        //cerr << ai.var_infos[0].occurences[0].sentence << endl;
        while ("Elvis Lives") {
          //  cerr << "baam" << endl;
            while (level_size.size > 0 && 
                   level_size.back() == 0) {
                level_size.pop();
                const int level_id = level_size.size - 1;
                if (level_id >= 0) {
                    unban(ai.binding_order[level_id]);
                }
            }
            if (level_size.size == 0) break;
            const int level_id = level_size.size - 1;
            assert(level_size.back() > 0);
            --level_size.back();
            //cerr << "biim" << endl;
            if (level_id == vars_n() - 1) {
                //cerr << "bwum" << endl;
                DomainValuation new_valuation;
                for (int vi: ai.domain_filling_pattern) {
                    if (vi > 0) {
                        --vi;
                        const auto &oc = ai.var_infos[vi].occurences[0];
         //               cerr << vi << endl;
         //               cerr << oc.sentence << endl;
         //               cerr << "XOO: " << oc.index << " " << ai.var_infos[vi].occurences.size << endl;
                        const auto &ib = bounds_stack.back()[oc.sentence];
                        assert(ib.first + 1 == ib.second);
                        new_valuation.append(
                            valuations_sets[oc.sentence]->at(
                                indices[oc.sentence][ib.first]
                            )[oc.index]
                        );
                    } else if (vi < 0) {
                        new_valuation.append(-vi - 1);
                    } else {
                        assert(0);
                    }
                }
                new_valuations.push_back(new_valuation);
                bounds_stack.pop();
            } else {
                //cerr << "buum" << endl;
                ban_by_var(ai.binding_order[level_id]);
                size_t base = bounds_stack.size - 1;
                split_by_var(ai.binding_order[level_id + 1]);
                level_size.append(bounds_stack.size - base);
            }
        }
        apply_new_valuations();
    }

};


void fill_domains(const vector<HighNode> &rules) {
   collect_initial_valuations(rules);
   //cerr << "initial valuations collected" << endl;
   vector<AlignmentInfo> alignment_infos = collect_alignment_infos(rules);
   void *memory = malloc(sizeof(Aligner));
   int total_valuations_found = 0;
   while ("Elvis Lives") {
       //cerr << "iteration done" << endl;
       size_t to_be_processed_index = 0;
       for (size_t i = 0; i < alignment_infos.size(); ++i) {
           if (alignment_infos[i].sources_new_valuations_n > 
               alignment_infos[to_be_processed_index].sources_new_valuations_n) {
               to_be_processed_index = i;
           }
       }
       if (alignment_infos[to_be_processed_index].sources_new_valuations_n == 0) {
           break;
       }
       AlignmentInfo &to_be_processed = alignment_infos[to_be_processed_index];

       Domain &to_recompute = domain_map[to_be_processed.destination_sentence];
       //cerr << "doing: " << domain_map[to_be_processed.destination_theorem].pattern << endl;
       int old_valuations_n = to_recompute.valuations.size();
       (new(memory) Aligner(to_be_processed))->recompute();
       to_be_processed.sources_new_valuations_n = 0;
       int valuations_n_delta = to_recompute.valuations.size() - old_valuations_n;
       total_valuations_found += valuations_n_delta;
       //cerr << "new valuations n: " << valuations_n_delta << endl;
       //cerr << "total valuations n: " << total_valuations_found << endl;
       //cerr << "resulting theorem valuations: \n" << domain_map[to_be_processed.destination_theorem].to_full_string() << endl;
       //cerr << "resulting domain valuations: \n" << domain_map[to_be_processed.destination_sentence].to_full_string() << endl;
       for (auto &ai: alignment_infos) {
           if (ai.source_sentences.contains(to_recompute.id)) {
               ai.sources_new_valuations_n += valuations_n_delta;
           }
       }
   }
   free(memory);
}

void print_solved_theorems(const vector<HighNode> &rules) {
    unordered_set<string> printed_strings;
    for (auto &rule: rules) {
        string to_print;
        const auto &dom = domain_map[rule.domain_hash]; 
        if (rule.type != TYPE::THEOREM) {
            assert(rule.type == TYPE::SENTENCE);
            to_print = "( <= " + rule.to_string() + " )\n";
        } else {
            to_print = dom.to_full_string();
        }
        if (printed_strings.count(to_print) == 0) {
            printed_strings.insert(to_print);
            cout << to_print;
        }
    }
}


int main(int argc, char **argv) {
    if (argc < 2) {
        cerr << "no input provided" << endl;
        return 1;
    }
    vector<GDLToken> rule_tokens;
    GDLTokenizer::tokenize(argv[1], rule_tokens);
//    for (const auto &token: rule_tokens) {
//        cerr << token.to_nice_string() + "\n";
//    }
//    cerr << "XXXX" << endl;
    vector<HighNode> rules = HighNode::generate_from_tokens(rule_tokens); 
    collect_domain_types(rules);
//    cerr << rules.size() << endl;
    fill_domains(rules);
    print_solved_theorems(rules);
    return 0;
}
