#include <iostream>
#include <fstream>
#include <unordered_map>

using namespace std;
#include "common.hpp"

const unordered_map<string, int> &numeric_rename = globals().numeric_rename;
const int MAX_FLAT_RULES_SIZE = 1000000;

namespace SENTENCE_TYPE {
    enum {
        NORMAL,
        DOES,
        TRUE,
        NEXT,
        LEGAL,
        TERMINAL,
        GOAL,
        INIT,
        N_SENTENCE_TYPES
    }
};

struct ForwardList {
    int sentence_id;
    short counter_max;
    short counter_value;
    bool bad, always_false;
    ForwardList(int _sentence_id, short _counter_max, bool _always_false) {
        sentence_id = _sentence_id;
        counter_max = _counter_max;
        always_false = _always_false;
        bad = false;
        counter_value = false;
    }
};

struct BootstrapForwardPropData {
    vector<ForwardList> counters;
    vector<vector<int>> dependencies;
    vecotr<int> types;
    vector<int> theorems_n;
};

const int NOT_TOKEN_ID = str_token_to_int("not"); 
const int DISTINCT_TOKEN_ID = str_token_to_int("distinct");
const int NEXT_TOKEN_ID = str_token_to_int("next");
const int LEGAL_TOKEN_ID = str_token_to_int("legal");

vector<bool> debug_always_true_sentence;
vector<bool> debug_always_false_sentence;
vector<bool> debug_always_false_theorem;
vector<bool> debug_always_true_theorem;

template <typename T> int sgn(T val) {
    return (T(0) < val) - (val < T(0));
}

unordered_map<string, int> sentence_ids;
unordered_map<int, int> value_to_theo_type;

void prepare_value_to_theo_type_map() {
    vector<pair<const char*, int>> to_init = {
        make_pair("does", SENTENCE_TYPE::DOES),
        make_pair("true", SENTENCE_TYPE::TRUE),
        make_pair("next", SENTENCE_TYPE::NEXT),
        make_pair("legal", SENTENCE_TYPE::LEGAL),
        make_pair("terminal", SENTENCE_TYPE::TERMINAL),
        make_pair("goal", SENTENCE_TYPE::GOAL),
        make_pair("init", SENTENCE_TYPE::INIT),
    };
    for (const auto & p: to_init) {
        value_to_theo_type[p.second] = str_token_to_int(p.first);
    }
}

int get_theo_type(const HighNode &node) {
    assert(node.type == TYPE::THEOREM);
    const auto first_val = node.sub[0].value;
    if (value_to_theo_type.count(first_val) > 0) {
        return value_to_theo_type[first_val];
    } else {
        return SENTENCE_TYPE::NORMAL;
    }
}

void generate_sentence_ids(const string &in_filename) {
    prepare_value_to_theo_type_map();
    ifstream inpf(in_filename);

    LimitedArray<vector<string>, N_SENTENCE_TYPES> by_theo_type;
    unordered_set<string> checked_sentences;
    by_theo_type.resize(N_SENTENCE_TYPES);

    vector<GDLToken> tokens;
    string line;
    while (getline(inpf, line)) {
        tokens.resize(0);
        GDLTokenizer::tokenize_str(line, tokens);
        HighNode node;
        node.fill_from_token(tokens[0]);
        const string sentence_str = node.sub[0].to_string();
        const int theo_type = get_theo_type(node);
        if (checked_sentences.count(sentence) == 0) {
            by_theo_type[theo_type].push_back(sentence_str);
        }
    }
    checked_sentences.clear();
    int id_counter = 1;
    for (int theo_type = 0; theo_type < N_SENTENCE_TYPES; ++theo_type) {
        const auto &sentence_strs = by_theo_type[theo_type];
        for (const auto &sentence: sentence_strs) {
            sentence_ids[sentence] = id_counter++;
        }
    }
}


// returns -id if negated
// distinct == 1 if normal distinct
// distinct == -1 if negated distinct
int get_sub_sentence_smart_id(const HighNode &snode, int &distinct) {
    distinct = 0;
    if (snode.value == DISTINCT_TOKEN_ID) {
        distinct = 1;
        return 0;
    }
    if (snode.value == NOT_TOKEN_ID) {
        assert(snode.sub.size() > 0);
        int ret = -get_sub_sentence_smart_id(snode.sub[0], distinct);
        distinct = -distinct;
        return ret;
    }
    return sentences_ids[snode.to_string()];
}

void load_bootstrap_forward_prop_data(const string &in_filename, 
                                      BootstrapForwardPropData &to_fill) {
    // remove distinct (bc, always true)
    const int max_sentence_id = sentence_ids.size();
    to_fill.counters.resize(0);
    to_fill.dependencies.resize(max_sentence_id + 1);
    to_fill.types.resize(max_sentence_id + 1);
    to_fill.counters.push_back(ForwardList(0, 0, true)); // dummy theorem 0
    to_fill.theorems_n.resize(0);
    to_fill.theorems_n.resize(max_sentence_id + 1);
    ifstream inpf(in_filename);
    vector<GDLToken> tokens;
    string line;
    int theorem_id = 1;
    while (getline(inpf, line)) {
        tokens.resize(0);
        GDLTokenizer::tokenize_str(line, tokens);
        HighNode node;
        node.fill_from_token(tokens[0]);
        int head_id = sentence_ids[node.sub[0].to_string()];
        to_fill.types[head_id] = get_theo_type(node);
        ++to_fill.theorems_n[head_id];
        bool always_false = false;
        int forward_counter = 0;
        for (int i = 1; i < node.sub.size(); ++i) {
            const auto &snode = node.sub[i];
            assert(snode.value != NEXT_TOKEN_ID);
            assert(snode.value != LEGAL_TOKEN_ID);
            int distinct;
            const int sub_sentence_id = get_sub_sentence_id(snode, distinct);
            if (sub_sentence_id == 0) {
                assert(distinct == 1 || distinct == -1);
                if (distinct == -1) { // this theorem is always false
                    always_false = true;
                    break;
                } else {
                    assert(distinct == 1);
                    continue; // skip sentence, because it is always true
                }
            } else {
                ++forward_counter;
                to_fill.dependencies[abs(sub_sentence_id)].push_back(
                        sgn(sub_sentence_id) * theorem_id);
            }
        }
        to_fill.counters.push_back(ForwardList(head_id, forward_counter, always_false));
        ++theorem_id;
        assert(to_fill.counters.size() == theorem_id);
    }
}


void find_ids_to_remove(BootstrapForwardPropData &bpfd, 
        vector<bool> &theo_ids_to_remove, vector<bool> &sentence_ids_to_remove) {
    vector<pair<int, bool>> const_sentences_queue;
    int theorem_id = 1;

    debug_always_true_sentence.resize(0);
    debug_always_true_sentence.resize(bfpd.types.size())
    debug_always_false_sentence.resize(0);
    debug_always_false_sentence.resize(bfpd.types.size());

    debug_always_true_theorem.resize(0);
    debug_always_true_theorem.resize(bfpd.counters.size());
    debug_always_false_theorem.resize(0);
    debug_always_false_theorem.resize(bfpd.counters.size());

    for (const auto &forward: bpfd.counters) {
        int sentence_to_append = 0;
        if (bpdf.types[forward.sentence_id] == SENTENCE_TYPE::INIT) {
            // skip init statements
            assert(forward.counter_max == 0);
            assert(!forward.always_false);
            continue;
        }
        if (bpdf.types[forward.sentence_id] == SENTENCE_TYPE::NEXT) {
            // leave const next because they are messy
            continue;
        }
        assert(bpdf.types[forward.sentence_id] != SENTENCE_TYPE::TRUE && 
               bpdf.types[forward.sentence_id] != SENTENCE_TYPE::DOES);

        if (forward.always_false) {
            theo_ids_to_remove[theorem_id] = true;
            debug_always_false_theorem[theorem_id] = true;
            assert(bfpd.theorems_n[forward.sentence_id] > 0);
            --bfpd.theorems_n[forward.sentence_id];
            if (bfpd.theorems_n[forward.sentence_id] == 0) {
                sentence_ids_to_remove[forward.sentence_id] = true;
                debug_always_false_sentence[forward.sentence_id] = true;
                const_sentences_queue.push_back(make_pair(forward.sentence_id, false));
            }
        }
        if (forward.counter_max == 0) {
            theo_ids_to_remove[theorem_id] = true;
            debug_always_true_theorem[theorem_id] = true;
            debug_always_true_sentence[forward.sentence_id] = true;
            if (sentence_ids_to_remove[forward.sentence_id] == false) {
                sentence_ids_to_remove[forward.sentence_id] = true;
                const_sentences_queue.push_back(make_pair(forward.sentence_id, true));
            }
        }
        ++theorem_id;
    }
    while (!const_sentences_queue.empty()) {
        const auto to_process = const_sentences_queue.back();
        const_sentences_queue.pop_back();
        const int sentence_id = to_process.first;
        const bool sentence_value = to_process.second;
        
        :qa
        :qa
    }
}


void remove_const_sentences(const string &in_filename) {
    // remove normal and next which are always true, assert there is no always true does
    // if there is always true legal, terminal, goal, init or next- leave it
    // remove distinct (because it is always true)
    BootstrapForwardPropData bfpd;
    load_bootstrap_forward_prop_data(in_filename, bfpd);
    vector<bool> theo_ids_to_remove;
    vector<bool> sentence_ids_to_remove;
    theo_ids_to_remove.resize(bfpd.counters.size());
    sentence_ids_to_remove.resize(bfpd.types.size());
    find_ids_to_remove(bfpd, theo_ids_to_remove, sentence_ids_to_remove);
}

int main(int argc, char **argv) {
    if (argc < 3) {
        cerr << "usage: " << argv[0] << " INPUT OUTPUT\n";
        return 1;
    }
    generate_sentence_ids(argv[1]);

    // filter out always true
    // split by:
    // * does (input)
    // * true (input)
    // * next (output)
    // * legal (output)
    // * normal 
    // * terminal
    // * goal
    // * init
    
    return 0;
}
