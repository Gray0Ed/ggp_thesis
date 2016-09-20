#include <iostream>
#include <fstream>
#include <unordered_map>


#ifndef NO_BACKWARD
#define BACKWARD_HAS_DW 1
#include "backward.hpp"

namespace backward {
    backward::SignalHandling sh;
};

#endif


using namespace std;
#include "common.hpp"
#include "HighNode.hpp"

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
    };
};

struct TheoremCounters {
    int sentence_id;
    short counter_max;
    short counter_value;
    bool bad, always_false;
    TheoremCounters() {
        sentence_id = 0;
    }
    TheoremCounters(int _sentence_id, short _counter_max, bool _always_false) {
        sentence_id = _sentence_id;
        counter_max = _counter_max;
        always_false = _always_false;
        bad = false;
        counter_value = 0;
    }
};

struct BootstrapPropData {
    vector<TheoremCounters> counters;
    vector<vector<int>> forward_deps;
    vector<vector<int>> dependencies;
    vector<int> types;
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
vector<string> sentence_id_to_str;
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

    LimitedArray<vector<string>, SENTENCE_TYPE::N_SENTENCE_TYPES> by_theo_type;
    unordered_set<string> checked_sentences;
    by_theo_type.resize(SENTENCE_TYPE::N_SENTENCE_TYPES);

    vector<GDLToken> tokens;
    string line;
    while (getline(inpf, line)) {
        tokens.resize(0);
        GDLTokenizer::tokenize_str(line, tokens);
        HighNode node;
        node.fill_from_token(tokens[0]);
        const string sentence_str = node.sub[0].to_string();
        const int theo_type = get_theo_type(node);
        if (checked_sentences.count(sentence_str) == 0) {
            by_theo_type[theo_type].push_back(sentence_str);
        }
    }
    checked_sentences.clear();
    int id_counter = 1;
    sentence_id_to_str.push_back("$NOPE$!!!");
    for (int theo_type = 0; theo_type < SENTENCE_TYPE::N_SENTENCE_TYPES; ++theo_type) {
        const auto &sentence_strs = by_theo_type[theo_type];
        for (const auto &sentence: sentence_strs) {
            sentence_ids[sentence] = id_counter++;
            sentence_id_to_str.push_back(sentence);
            assert(sentence_id_to_str[id_counter - 1] == sentence);
        }
    }
}

namespace SUB_SENTENCE_FLAG  {
    enum {
        NORMAL,
        NEGATED,
        ALWAYS_FALSE,
        ALWAYS_TRUE,
    };
};

int get_sub_sentence_id(const HighNode &snode, int &flag) {
    if (snode.value == DISTINCT_TOKEN_ID) {
        flag = SUB_SENTENCE_FLAG::ALWAYS_TRUE;
        return 0;
    }
    if (snode.value == NOT_TOKEN_ID) {
        assert(snode.sub.size() > 0);
        int ret = get_sub_sentence_id(snode.sub[0], flag);
        if (flag == SUB_SENTENCE_FLAG::NEGATED) {
            flag = SUB_SENTENCE_FLAG::NORMAL;
        } else if (flag == SUB_SENTENCE_FLAG::NORMAL) {
            flag = SUB_SENTENCE_FLAG::NEGATED;
        } else if (flag == SUB_SENTENCE_FLAG::ALWAYS_FALSE) {
            flag = SUB_SENTENCE_FLAG::ALWAYS_TRUE;
        } else if (flag == SUB_SENTENCE_FLAG::ALWAYS_TRUE) {
            flag = SUB_SENTENCE_FLAG::ALWAYS_FALSE;
        } else {
            assert(false);
        }
        return ret;
    }
    const string snode_string = snode.to_string();
    if (sentence_ids.count(snode_string) == 0) {
        flag = SUB_SENTENCE_FLAG::ALWAYS_FALSE;
        return 0;
    } else {
        flag = SUB_SENTENCE_FLAG::NORMAL;
        return sentence_ids[snode.to_string()];
    }
}

void load_bootstrap_prop_data(const string &in_filename, 
                              BootstrapPropData &to_fill) {
    // remove distinct (bc, always true)
    const int max_sentence_id = sentence_ids.size();
    to_fill.counters.resize(0);
    to_fill.counters.push_back(TheoremCounters(0, 0, true)); // dummy theorem 0
    to_fill.dependencies.resize(0);
    to_fill.dependencies.push_back(vector<int>());
    to_fill.forward_deps.resize(max_sentence_id + 1);
    to_fill.types.resize(max_sentence_id + 1);
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
        to_fill.dependencies.push_back(vector<int>());
        for (size_t i = 1; i < node.sub.size(); ++i) {
            const auto &snode = node.sub[i];
            assert(snode.value != NEXT_TOKEN_ID);
            assert(snode.value != LEGAL_TOKEN_ID);
            int flag;
            const int sub_sentence_id = get_sub_sentence_id(snode, flag);
            if (flag == SUB_SENTENCE_FLAG::ALWAYS_TRUE) {
                continue; // skip sentence, because it is always true
            } else if (flag == SUB_SENTENCE_FLAG::ALWAYS_FALSE) {
                always_false = true;
                break;
            }  else {
                assert(flag == SUB_SENTENCE_FLAG::NORMAL ||
                       flag == SUB_SENTENCE_FLAG::NEGATED);
                int mult = 1;
                if (flag == SUB_SENTENCE_FLAG::NEGATED) {
                    mult = -1;
                }
                ++forward_counter;
                to_fill.forward_deps[sub_sentence_id].push_back(mult * theorem_id);
                to_fill.dependencies.back().push_back(mult * sub_sentence_id);
            }
        }
        to_fill.counters.push_back(TheoremCounters(head_id, forward_counter, always_false));
        ++theorem_id;
        assert((int)to_fill.counters.size() == theorem_id);
    }
}


void find_ids_to_remove(BootstrapPropData &bpd, 
        vector<bool> &const_theos, vector<bool> &const_sentences) {
    vector<pair<int, bool>> const_sentences_queue;
    int theorem_id = 1;

    debug_always_true_sentence.resize(0);
    debug_always_true_sentence.resize(bpd.types.size());
    debug_always_false_sentence.resize(0);
    debug_always_false_sentence.resize(bpd.types.size());

    debug_always_true_theorem.resize(0);
    debug_always_true_theorem.resize(bpd.counters.size());
    debug_always_false_theorem.resize(0);
    debug_always_false_theorem.resize(bpd.counters.size());

    for (const auto &forward: bpd.counters) {
        if (bpd.types[forward.sentence_id] == SENTENCE_TYPE::INIT) {
            // skip init statements
            assert(forward.counter_max == 0);
            assert(!forward.always_false);
            continue;
        }
        if (bpd.types[forward.sentence_id] == SENTENCE_TYPE::NEXT) {
            // leave const next because they are messy
            continue;
        }
        assert(bpd.types[forward.sentence_id] != SENTENCE_TYPE::TRUE && 
               bpd.types[forward.sentence_id] != SENTENCE_TYPE::DOES);

        if (forward.always_false) {
            const_theos[theorem_id] = true;
            debug_always_false_theorem[theorem_id] = true;
            assert(bpd.theorems_n[forward.sentence_id] > 0);
            --bpd.theorems_n[forward.sentence_id];
            if (bpd.theorems_n[forward.sentence_id] == 0) {
                const_sentences[forward.sentence_id] = true;
                debug_always_false_sentence[forward.sentence_id] = true;
                const_sentences_queue.push_back(make_pair(forward.sentence_id, false));
            }
        }
        if (forward.counter_max == 0) {
            const_theos[theorem_id] = true;
            debug_always_true_theorem[theorem_id] = true;
            debug_always_true_sentence[forward.sentence_id] = true;
            if (const_sentences[forward.sentence_id] == false) {
                const_sentences[forward.sentence_id] = true;
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
        const auto &deps = bpd.forward_deps[sentence_id];
        for (int theo_id: deps) {
            if (!sentence_value) {
                theo_id = -theo_id;
            }
            if (theo_id > 0) {
                auto &tcounter = bpd.counters[theo_id];
                ++tcounter.counter_value;
                assert(tcounter.counter_value <= tcounter.counter_max);
                if (tcounter.counter_value == tcounter.counter_max) {
                    const_theos[theo_id] = true;
                    assert(!const_sentences[tcounter.sentence_id]);
                    const_sentences[tcounter.sentence_id] = true;
                    debug_always_true_theorem[theo_id] = true;
                    debug_always_true_sentence[tcounter.sentence_id] = true;
                    const_sentences_queue.push_back(make_pair(tcounter.sentence_id, true));
                }
            } else {
                assert(theo_id < 0);
                theo_id = -theo_id;
                int dep_sentence_id = bpd.counters[theo_id].sentence_id;
                debug_always_false_theorem[theo_id] = true;
                const_theos[theo_id] = true;
                --bpd.theorems_n[dep_sentence_id];
                assert(bpd.theorems_n[dep_sentence_id] >= 0);
                if (bpd.theorems_n[dep_sentence_id] == 0) {
                    debug_always_false_sentence[dep_sentence_id] = true;
                    assert(!const_sentences[dep_sentence_id]);
                    const_sentences[dep_sentence_id] = true;
                    const_sentences_queue.push_back(make_pair(dep_sentence_id, false));
                }
            }
        }
    }
}

string theorem_to_string(int theorem_id, const BootstrapPropData &bpd) {
    string res = "( <= ( ";
    res = sentence_id_to_str[bpd.counters[theorem_id].sentence_id] + " )";
    for (int deps: bpd.dependencies[theorem_id]) {
        int sentence_id = deps;
        res += "( ";
        if (deps < 0) {
            res += " not ( ";
            sentence_id *= -1;
        }
        res += sentence_id_to_str[sentence_id] + " )";
        if (deps < 0) {
            res += " )";
        }
    }
    return res;
}

void remove_const_sentences(const string &in_filename) {
    // remove const normal which, assert there is no always true does
    // if there is const legal, terminal, goal, init or next- leave it
    // remove distinct (because it is always true)
    BootstrapPropData bpd;
    load_bootstrap_prop_data(in_filename, bpd);

    vector<bool> const_theos;
    vector<bool> const_sentences;
    const_theos.resize(bpd.counters.size());
    const_sentences.resize(bpd.types.size());
    find_ids_to_remove(bpd, const_theos, const_sentences);
    for (int i = 1; i < (int)debug_always_true_sentence.size(); ++i) {
        assert((debug_always_true_sentence[i] || debug_always_false_sentence[i]) ==
               const_sentences[i]);
    }
    for (int i = 1; i < (int)debug_always_true_theorem.size(); ++i) {
        assert((debug_always_true_theorem[i] || debug_always_false_theorem[i]) ==
               const_theos[i]);
    }
    cerr << "CONST SENTENCES:\n";
    for (int i = 1; i < (int)const_sentences.size(); ++i) if (const_sentences[i]) {
        cerr << "always ";
        if (debug_always_true_sentence[i]) {
            cerr << "true: ";
        } else {
            assert(debug_always_false_sentence[i]);
            cerr << "false: ";
        }
        cerr << sentence_id_to_str[i] << "\n";
    }
    cerr << "CONST THEOREMS:\n";
    for (int i = 1; i < (int)const_theos.size(); ++i) if (const_theos[i]) {
        cerr << "always ";
        if (debug_always_true_theorem[i]) {
            cerr << "true: ";
        } else {
            assert(debug_always_false_theorem[i]);
            cerr << "false: ";
        }
        cerr << theorem_to_string(i, bpd) << "\n";
    }
}

int main(int argc, char **argv) {
    if (argc < 3) {
        cerr << "usage: " << argv[0] << " INPUT OUTPUT\n";
        return 1;
    }
    generate_sentence_ids(argv[1]);
    remove_const_sentences(argv[1]);

    // filter out const sentences and theorems
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
