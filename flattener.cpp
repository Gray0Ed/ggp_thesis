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

#include "LimitedArray.hpp"

#define BACKWARD_HAS_DW 1
#include "backward.hpp"

namespace backward {
    backward::SignalHandling sh;
};

using namespace std;
string input;
const int MAX_DOMAIN_VARS = 20;
const int MAX_SENTENCES_IN_THEOREM = 10;
const int MAX_TERMS_N = 100000;

hash<string> str_hasher;
typedef LimitedArray<short, MAX_DOMAIN_VARS> DomainValuation;

unordered_map<string, int> numeric_rename;
vector<string> reverse_numeric_rename;

struct Token {
    string val;
    vector<Token> sub;

    string to_string(int ntabs=0) const {
        string res = val + ":\n";
        for (const Token & t: sub) {
            res += t.to_string(ntabs + 1);
        }
        res.insert(0, ntabs, ' ');
        return res;
    }

    bool leaf() const {
        return sub.empty();
    }

    //string &operator()(int i) {
    //    assert(sub.size() >= 0);
    //    assert(i < sub.size() && i >= 0);
    //    return sub[i].val;
    //}

    string operator()(int i) const {
        assert(sub.size() >= 0);
        assert(i < sub.size() && i >= 0);
        return sub[i].val;
    }

    void shorten_edges() {
        for (Token &t : sub) {
            t.shorten_edges();
        }
        if (sub.size() == 1) {
            *this = sub[0];
        }
    }
};


bool is_whitespace(char c) {
    return isspace(c);
}

bool is_name_char(char c) {
    return !is_whitespace(c) && c != '(' && c != ')';
}

int _tokenize(int c, Token &to_fill) {
    if (input.size() == c) return c;
    char cur = input[c];
    if (cur == '(') {
        to_fill.sub.push_back(Token());
        return _tokenize(_tokenize(c + 1, to_fill.sub.back()), to_fill);
    } else if (cur == ')') {
        return c + 1;
    } else if (is_whitespace(cur)) {
        return _tokenize(c + 1, to_fill);
    } else {
        int s = c;
        while (c < input.size() && is_name_char(input[c])) {
            ++c;
        }
        to_fill.sub.push_back(Token());
        to_fill.sub.back().val = input.substr(s, c - s);
        return _tokenize(c, to_fill);
    }
}

void tokenize(Token &root) {
    assert(_tokenize(0, root) == input.size());
    root.shorten_edges();
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

    string to_string_with_valuation(const DomainValuation &valuation) {
        string pattern = to_string();
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
        int s = numeric_rename.size();
        numeric_rename[token] = s;
        reverse_numeric_rename.push_back(token);
        assert(reverse_numeric_rename.size() == s + 1);
        assert(s <= SHRT_MAX);
    }
    return numeric_rename[token];
}

struct HighNode {
    int type;
    int theorem_vars_n;
    size_t domain_hash;
    string domain_pattern;
    int value;
    int exp_var_id;
    bool contains_variable;
    Token debug_token;
    vector<HighNode> sub;

    void fill_from_token(const Token &t, 
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
            for (int i = 1; i < t.sub.size(); ++i) {
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
            for (int i = 1; i < t.sub.size(); ++i) {
                sub[i - 1].fill_from_token(t.sub[i], var_mapping, TYPE::TUPLE);
                contains_variable = contains_variable || sub[i - 1].contains_variable;
            }
        }
        assert(type != TYPE::NONE);
    }

    static vector<HighNode> generate_from_root(const Token &root) {
        vector<HighNode> res;
        res.resize(root.sub.size());
        for (int i = 0; i < root.sub.size(); ++i) {
            unordered_map<int, int> var_mapping;
            res[i].fill_from_token(root.sub[i], var_mapping);
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
                res += " <=";
            }
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
        assert(res.find("next") == string::npos && 
               res.find("legal") == string::npos && res.find("init") == string::npos);
        return res;
    }

    void gather_base_valuations_from_consts(DomainValuation &to_fill) {
        for (HighNode &hn: sub) {
            assert(hn.type == TYPE::CONST || hn.type == TYPE::TUPLE);
            if (hn.type == TYPE::CONST) {
                to_fill.append(hn.value);
            } else {
                hn.gather_base_valuations_from_consts(to_fill);
            }
        }
    }

    void collect_distinct_info(LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos) {
        assert(reverse_numeric_rename[value] == "distinct");
        assert(sub.size() == 2);
        HighNode *left_node = &sub[0];
        HighNode *right_node = &sub[1];
        if (left_node->type == TYPE::CONST) {
            swap(left_node, right_node);
        }
        assert(left_node->type == TYPE::VAR);
        assert(right_node->type == TYPE::VAR || right_node->type == TYPE::CONST);
        int right_id = -right_node->value;
        if (right_node->type == TYPE::VAR) {
            right_id = right_node->exp_var_id;
        }
        var_infos[left_node->exp_var_id].different_than.append(right_id);
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

    AlignmentInfo alignment_info() {
        assert(type == TYPE::THEOREM);
        AlignmentInfo res;
        res.destination_theorem = domain_hash;
        res.destination_sentence = sub[0].domain_hash;
        res.sources_new_valuations_n = 0;
        res.var_infos.size = theorem_vars_n; 
        fill_var_in_dom_indices(res.domain_filling_pattern);
        sub[0].fill_var_occurences(res.var_infos, 0);
        auto &var_infos = res.var_infos;
        for (int i = 1; i < sub.size(); ++i) {
            const string & sub_svalue = reverse_numeric_rename[sub[i].value];
            if (sub_svalue == "not" || !sub[i].contains_variable) continue;
            if (sub_svalue == "distinct") {
                sub[i].collect_distinct_info(var_infos);
            } else {
                res.source_sentences.append(sub[i].domain_hash);
                res.sources_new_valuations_n += domain_map[sub[i].domain_hash].valuations.size();
                res.source_constraints.grow();
                sub[i].fill_var_constraints(res.source_constraints.back());
                sub[i].fill_var_occurences(var_infos, i);
            }
        }

        res.binding_order.size = theorem_vars_n;
        for (int i = 0; i < theorem_vars_n; ++i) {
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

void collect_initial_valuations(vector<HighNode> &rules) {
    for (HighNode &hn: rules) {
        if (hn.type == TYPE::SENTENCE) {
            DomainValuation new_valuation;
            hn.gather_base_valuations_from_consts(new_valuation);
            domain_map[hn.domain_hash].valuations.push_back(new_valuation);
        }
    }
}

vector<AlignmentInfo> collect_alignment_infos(vector<HighNode> &rules) {
    vector<AlignmentInfo> res;
    for (auto hn: rules) {
        if (hn.type == TYPE::THEOREM) {
            res.push_back(hn.alignment_info());
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

    typedef LimitedArray<pair<int, int>, MAX_SENTENCES_IN_THEOREM> IndexBound;
    LimitedArray<IndexBound, MAX_TERMS_N * 3> bounds_stack;

    int sentences_n() const {
        return ai.source_sentences.size;
    }

    int vars_n() const {
        return ai.var_infos.size;
    }

    void prepare_indices() {
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
        }
    }

    bool split_by_var(int split_by_var_id) {
        const auto &occurences = ai.var_infos[split_by_var_id].occurences;
        const auto &banned_values = banned_var_values[split_by_var_id];
        const IndexBound input_bounds = bounds_stack.back();
        bounds_stack.pop();
        assert(occurences.size > 0);
        for (const auto &occurence: occurences) {
            const auto &bound = input_bounds[occurence.sentence];
            auto &sindices = indices[occurence.sentence];
            auto &valuation_set = *valuations_sets[occurence.sentence];
            sort(&sindices[0] + bound.first, &sindices[0] + bound.second, 
                [&valuation_set, &occurence](const auto &a, const auto &b) -> bool {
                    return valuation_set[a][occurence.index] < valuation_set[b][occurence.index];
                }
            );
        }
        LimitedArray<int, MAX_SENTENCES_IN_THEOREM> processed_index;
        for (int i = 0; i < sentences_n(); ++i) {
            processed_index.append(0);
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
            memset(&ib_to_fill[0], 0xff, sentences_n() * sizeof(pair<int, int>));
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

    void recompute() {
        vector<DomainValuation> new_valuations;
        indices.size = valuations_sets.size = sentences_n();
        prepare_indices();

        banned_var_values.resize(vars_n());

        bounds_stack.resize(1);
        bounds_stack[0].resize(vars_n());
        for (int i = 0; i < vars_n(); ++i) {
            bounds_stack[0][i].first = 0;
            bounds_stack[0][i].second = indices[i].size;
        }
        split_by_var(ai.binding_order[0]);
        LimitedArray<int, MAX_DOMAIN_VARS> last_bound_index;
        last_bound_index.append(bounds_stack.size - 1);
        while ("Elvis Lives") {
            while (last_bound_index.size > 0 && 
                   last_bound_index.back() > bounds_stack.size - 1) {
                last_bound_index.pop();
                const int level_id = last_bound_index.size - 1;
                if (level_id >= 0) {
                    unban(ai.binding_order[level_id]);
                }
            }
            if (last_bound_index.size == 0) break;
            const int level_id = last_bound_index.size - 1;
            const int binded_var_id = ai.binding_order[level_id];
            int lower_limit = 1;
            if (last_bound_index.size > 1) {
                lower_limit = last_bound_index.back(1) + 1;
            }
            if (last_bound_index.back() > lower_limit) {
                --last_bound_index.back();
            }
            if (level_id == vars_n() - 1) {
                DomainValuation new_valuation;
                for (int vi: ai.domain_filling_pattern) {
                    if (vi > 0) {
                        --vi;
                        const auto &oc = ai.var_infos[vi].occurences[0];
                        const auto &ib = bounds_stack.back()[oc.sentence];
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
            } else {
                ban_by_var(binded_var_id);
                size_t obs = bounds_stack.size;
                split_by_var(binded_var_id);
                last_bound_index.append(max(obs, bounds_stack.size) - 1);
            }
        }
        auto &dt = domain_map[ai.destination_theorem];
        auto &ds = domain_map[ai.destination_sentence];
        
        dt.valuations = new_valuations;
        for (auto & new_valuation: new_valuations) {
            new_valuation.resize(ds.valuation_size);
            ds.valuations.push_back(new_valuation);
        }
        sort(ds.valuations.begin(), ds.valuations.end());
        unique(ds.valuations.begin(), ds.valuations.end());
    }

};



void fill_domains(vector<HighNode> &rules) {
   collect_initial_valuations(rules);
   cerr << "initial valuations collected" << endl;
   for (auto & dm: domain_map) {
       cerr << dm.second.to_string();
   }
   vector<AlignmentInfo> alignment_infos = collect_alignment_infos(rules);
   while ("Elvis Lives") {
       int biggest_change = 0;
       AlignmentInfo *to_be_processed = 0;
       for (auto &ai: alignment_infos) {
           if (ai.sources_new_valuations_n > biggest_change) {
               biggest_change = ai.sources_new_valuations_n;
               to_be_processed = &ai;
           }
       }
       if (to_be_processed == 0) {
           break;
       }

       Domain &to_recompute = domain_map[to_be_processed->destination_sentence];
       int old_valuations_n = to_recompute.valuations.size();
       Aligner(*to_be_processed).recompute();
       to_be_processed->sources_new_valuations_n = 0;
       int valuations_n_delta = to_recompute.valuations.size() - old_valuations_n;
       for (auto &ai: alignment_infos) {
           if (ai.source_sentences.contains(to_recompute.id)) {
               ai.sources_new_valuations_n += valuations_n_delta;
           }
       }
   }
}

void print_solved_theorems(const vector<HighNode> &rules) {
    for (auto &rule: rules) {
        if (rule.type != TYPE::THEOREM) continue;
        for (const auto &valuation: domain_map[rule.domain_hash].valuations) {
            cerr << domain_map[rule.domain_hash].to_string_with_valuation(valuation) << '\n';
        }
    }
}


int main(int argc, char **argv) {
    if (argc < 2) {
        cerr << "no input provided" << endl;
        return 1;
    }
    ifstream inp(argv[1]);
    input = string((istreambuf_iterator<char>(inp)),
            istreambuf_iterator<char>());
   // Token root;
   // tokenize(root);
// //   root.shorten_edges();
   // cerr << root.to_string() << endl;
   // vector<HighNode> rules = HighNode::generate_from_root(root); 
   // collect_domain_types(rules);
   // for (auto & hn: rules) {
   //     cerr << hn.domain_pattern << endl;
   // }
   // cerr << rules.size() << endl;
    vector<HighNode> bum;
    fill_domains(bum);
//    print_solved_theorems(rules);
    return 0;
}
