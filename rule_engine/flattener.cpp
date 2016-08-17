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

#include "MyArrays.hpp"
#include "GDLTokenizer.hpp"
#include "common.hpp"
#include "Aligner.hpp"

using namespace std;

const int MAX_DOMAIN_VARS = 80;
const int MAX_SENTENCES_IN_THEOREM = 15;
const int MAX_TERMS_N = 10000;

hash<string> str_hasher;

unordered_map<size_t, Domain*> domain_map;
unordered_map<string, int> numeric_rename;
vector<string> reverse_numeric_rename;

void replace_first_occurence(string &to_modify, const string &to_replace,
                             const string &replacement) {
    auto pos = to_modify.find(to_replace);
    if (pos != string::npos) {
        to_modify.replace(pos, to_replace.size(), replacement);
    }
}

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
            domain_map[domain_hash] = new Domain(domain_pattern, domain_type);
            if (checker.count(domain_hash) == 0) {
                checker[domain_hash] = unordered_set<string>();
            }
            checker[domain_hash].insert(domain_pattern);
            assert(domain_map[domain_hash]->id == domain_hash);
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
                res.source_sentences.append(domain_map[sub[i].domain_hash]);
                res.sources_new_valuations_n += domain_map[sub[i].domain_hash]->valuations.size();
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
            domain_map[hn.domain_hash]->valuations.push_back(new_valuation);
        }
    }
}

void collect_alignment_infos(const vector<HighNode> &rules, vector<AlignmentInfo> &res) {
    res.resize(0);
    res.reserve(100);
    for (const auto &hn: rules) {
        if (hn.type == TYPE::THEOREM) {
            res.push_back(hn.alignment_info());
            //cerr << res.back().sources_new_valuations_n << endl;
            //cerr << hn.domain_pattern << endl;
            //cerr << domain_map[hn.sub[0].domain_hash].to_string();
        }
    }
}

void fill_domains(const vector<HighNode> &rules) {
    collect_initial_valuations(rules);
    vector<AlignmentInfo> alignment_infos;
    collect_alignment_infos(rules, alignment_infos);
    fix_point_align(alignment_infos);
}

void print_solved_theorems(const vector<HighNode> &rules) {
    unordered_set<string> printed_strings;
    for (auto &rule: rules) {
        string to_print;
        const auto &dom = *domain_map[rule.domain_hash]; 
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
