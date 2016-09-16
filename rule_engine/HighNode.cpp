#include "HighNode.hpp"
#include <climits>

static unordered_map<size_t, Domain*> &domain_map = globals().domain_map;
static unordered_map<string, int> &numeric_rename = globals().numeric_rename;
static vector<string> &reverse_numeric_rename = globals().reverse_numeric_rename;

int str_token_to_int(const string &token) {
    if (numeric_rename.count(token) == 0) {
        size_t s = numeric_rename.size();
        numeric_rename[token] = s;
        reverse_numeric_rename.push_back(token);
        assert(reverse_numeric_rename.size() == s + 1);
        assert(s <= SHRT_MAX);
    }
    return numeric_rename[token];
}

string HighNode::to_string() const {
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

void HighNode::fill_from_token(const GDLToken &t, 
        unordered_map<int, int> &var_mapping,
        int induced_type) {
    debug_token = t;
    contains_variable = false;
    if (t.leaf()) {
        assert(!t.val.empty());
        int renamed = str_token_to_int(t.val);
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
        assert(t.sub.size() >= 2);
        assert(induced_type == TYPE::NONE);
        type = TYPE::THEOREM;
        sub.resize(t.sub.size() - 1);
        for (size_t i = 1; i < t.sub.size(); ++i) {
            sub[i - 1].fill_from_token(t.sub[i], var_mapping, TYPE::SENTENCE);
            contains_variable = contains_variable || sub[i - 1].contains_variable;
        }
        theorem_vars_n = var_mapping.size();
        // assuming that init expression doesn't require reasoning
        assert(t(1) != "init" || (t(1) == "init" && t.sub.size() == 2));
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
        value = str_token_to_int(t(0));
        sub.resize(t.sub.size() - 1);
        for (size_t i = 1; i < t.sub.size(); ++i) {
            sub[i - 1].fill_from_token(t.sub[i], var_mapping, TYPE::TUPLE);
            contains_variable = contains_variable || sub[i - 1].contains_variable;
        }
    }
    assert(type != TYPE::NONE);
    max_sub_size = max(max_sub_size, (int)sub.size());
    max_theorem_vars_n = theorem_vars_n;
    for (size_t i = 0; i < sub.size(); ++i) {
        max_sub_size = max(max_sub_size, sub[i].max_sub_size);
        max_theorem_vars_n = max(sub[i].max_theorem_vars_n, max_theorem_vars_n);
    }
}

vector<HighNode> HighNode::generate_from_tokens(const vector<GDLToken> &tokens) {
    vector<HighNode> res;
    res.reserve(tokens.size());
    int max_sentences = 0;
    int max_vars = 0;
    for (auto &tok: tokens) {
        unordered_map<int, int> var_mapping;
        res.push_back(HighNode());
        res.back().fill_from_token(tok, var_mapping);
        max_vars = max(max_vars, res.back().max_theorem_vars_n);
        max_sentences = max(max_sentences, res.back().max_sub_size);
    }
    cerr << "MAX SENTENCES: " << max_sentences << "\nMAX VARS: " << max_vars << endl;
    return res;
}

pair<string, string> HighNode::assign_domain_hash_and_pattern(
        unordered_map<size_t, unordered_set<string>> & checker) {
    string res;
    string ores; //without replaced next, init, legal
    if (type != TYPE::THEOREM) {
        res = reverse_numeric_rename[value];
    } else {
        res = "( <=";
    }
    ores = res;
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
            ores += " #";
        } else if (hn.type == TYPE::SENTENCE || hn.type == TYPE::TUPLE) {
            auto sub_pattern = hn.assign_domain_hash_and_pattern(checker);
            res += " ( " + sub_pattern.first + " )";
            ores += " ( " + sub_pattern.second + " )";
        } else {
            cerr << debug_token.to_string() << endl;
            cerr << hn.type << " " << hn.debug_token.to_string() << endl;
            assert(0);
        }
        if (type == TYPE::THEOREM && !first_done) {
            first_done = true;
            assert(hn.type == TYPE::SENTENCE);
        }
    }
    if (type == TYPE::THEOREM) {
        res += " )";
        ores += " )";
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
        if (domain_map.count(domain_hash) == 0) {
            domain_map[domain_hash] = new Domain(
                    domain_pattern, ores, domain_type);
        }
        if (checker.count(domain_hash) == 0) {
            checker[domain_hash] = unordered_set<string>();
        }
        checker[domain_hash].insert(domain_pattern);
        assert(domain_map[domain_hash]->id == domain_hash);
    }
    return make_pair(res, ores);
}

void HighNode::gather_base_valuations_from_consts(DomainValuation &to_fill) const {
    for (const HighNode &hn: sub) {
        assert(hn.type == TYPE::CONST || hn.type == TYPE::TUPLE);
        if (hn.type == TYPE::CONST) {
            to_fill.append(hn.value);
        } else {
            hn.gather_base_valuations_from_consts(to_fill);
        }
    }
}

void HighNode::collect_distinct_info(LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos) const {
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

void HighNode::fill_var_constraints(LimitedArray<VarConstraint, MAX_DOMAIN_VARS> &constraints) const {
    int index = 0;
    fill_var_constraints(constraints, index);
}

void HighNode::fill_var_constraints(
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

void HighNode::fill_var_occurences(
        LimitedArray<AlignmentVarInfo, MAX_DOMAIN_VARS> &var_infos, 
        int sentence_index) const {
    int var_index = 0;
    fill_var_occurences(var_infos, sentence_index, var_index);
}

void HighNode::fill_var_occurences(
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

void HighNode::fill_var_in_dom_indices(LimitedArray<int, MAX_DOMAIN_VARS> &to_fill) const {
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

void HighNode::fill_key_occurences(AlignmentVarInfo &var_info) const {
    if (var_info.occurences.size == 0) return;
    sort(var_info.occurences.begin(), var_info.occurences.end(), 
            [](const VarOccurence &va, const VarOccurence &vb) -> bool {
                return va.sentence < vb.sentence;
            });
    var_info.key_occurences = var_info.occurences;
    auto last = unique(var_info.key_occurences.begin(), var_info.key_occurences.end());
    while (&var_info.key_occurences.back() + 1 != last) {
        var_info.key_occurences.pop();
    }
}

void HighNode::fill_var_equivalence(AlignmentInfo &ai) const {
    ai.var_equivalence.resize(ai.source_sentences.size);
    for (size_t sentence_i = 0; sentence_i < ai.source_sentences.size; ++sentence_i) {
        ai.var_equivalence[sentence_i].resize(
            ai.source_sentences[sentence_i]->valuation_size);
        for (int v = 0; v < (int)ai.var_equivalence[sentence_i].size; ++v) {
            ai.var_equivalence[sentence_i][v] = v;
        }
    }

    for (const auto &vi: ai.var_infos) {
        assert(vi.occurences.size > 0);
        int current_sentence = vi.occurences[0].sentence;
        int first_index = vi.occurences[0].index;
        ai.var_equivalence[current_sentence][vi.occurences[0].index] = first_index;
        for (size_t oc_i = 1; oc_i < vi.occurences.size; ++oc_i) {
            if (vi.occurences[oc_i].sentence != current_sentence) {
                current_sentence = vi.occurences[oc_i].sentence;
                first_index = vi.occurences[oc_i].index;
            }
            ai.var_equivalence[current_sentence][vi.occurences[oc_i].index] = first_index;
        }
    }
}

AlignmentInfo HighNode::alignment_info() const {
    assert(type == TYPE::THEOREM);
    AlignmentInfo res;
    res.destination_theorem = domain_map[domain_hash];
    res.destination_sentence = domain_map[sub[0].domain_hash];
    res.sources_new_valuations_n = 1;
    res.var_infos.size = theorem_vars_n; 
    assert(res.source_sentences.size == 0);
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
            assert(res.source_sentences.back());
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
    for (auto &vi: res.var_infos) {
        fill_key_occurences(vi);
    }
    fill_var_equivalence(res);
    return res;
}

