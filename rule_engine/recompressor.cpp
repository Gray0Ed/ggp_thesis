#include <iostream>
#include <fstream>
#include <unordered_map>
#include <cstdlib>
#include <algorithm>

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
#include "recompressor.hpp"


struct TheoremData {
    int head_id;
    short counter_max;
    short counter_value;
    bool always_false;
    vector<int> right_side_sentence_ids; // -sentence_id if negated
    TheoremData() {
        head_id = -1;
    }
};

struct SentenceData {
    vector<int> containing_theorem_ids; // -theorem_id if negated
    vector<int> is_head_of_theorem_ids;
    int valid_is_head_of_counter;
};

string input_path;

namespace OutputPaths {
    string debug_info, propnet_data, backtrack_data, types_and_pairings;
};

int NOT_TOKEN_ID, DISTINCT_TOKEN_ID, NEXT_TOKEN_ID, LEGAL_TOKEN_ID;

unordered_map<string, int> sentence_ids;
vector<string> sentence_id_to_str;

unordered_map<int, int> value_to_theo_type;
vector<string> theorem_id_to_str;

vector<SentenceInfo> sentence_infos;
vector<SentenceData> sentence_datas;
vector<TheoremData> theorem_datas;

vector<bool> debug_always_true_sentence;
vector<bool> debug_always_false_sentence;
vector<bool> debug_always_false_theorem;
vector<bool> debug_always_true_theorem;
vector<bool> const_theos, const_sentences;
vector<int> theorem_remap, sentence_remap;
unordered_map<int, int> token_to_player_id;

int upper_sentence_id() {
    return sentence_id_to_str.size();
}

int upper_theorem_id() {
    return theorem_id_to_str.size();
}

void initialize_global_token_ids() {
    NOT_TOKEN_ID = str_token_to_int("not"); 
    DISTINCT_TOKEN_ID = str_token_to_int("distinct");
    NEXT_TOKEN_ID = str_token_to_int("next");
    LEGAL_TOKEN_ID = str_token_to_int("legal");
}

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
        value_to_theo_type[str_token_to_int(p.first)] = p.second;
    }
}

int get_sentence_type(const HighNode &node) {
    const auto first_val = node.value;
    if (value_to_theo_type.count(first_val) > 0) {
        return value_to_theo_type[first_val];
    } else {
        return SENTENCE_TYPE::NORMAL;
    }
}

HighNode &not_stripper(HighNode &to_strip) {
    if (to_strip.value == NOT_TOKEN_ID) {
        assert(to_strip.sub.size() == 1);
        return not_stripper(to_strip.sub[0]);
    } else {
        return to_strip;
    }
}

void get_equivalent_sentence_node(const HighNode &node, HighNode &res) {
    int stype = get_sentence_type(node);
    assert(is_with_equivalent_type(stype));
    int equivalent_token_id = -1;
    if (stype == SENTENCE_TYPE::INIT || stype == SENTENCE_TYPE::NEXT) {
        equivalent_token_id = str_token_to_int("true");
    }
    if (stype == SENTENCE_TYPE::TRUE) {
        equivalent_token_id = str_token_to_int("next");
    }
    if (stype == SENTENCE_TYPE::DOES) {
        equivalent_token_id = str_token_to_int("legal");
    }
    if (stype == SENTENCE_TYPE::LEGAL) {
        equivalent_token_id = str_token_to_int("does");
    }
    if (equivalent_token_id == -1) {
        assert(false);
    }
    res = node;
    res.value = equivalent_token_id;
}

int get_player_id(const HighNode &node) {
    // player ids are from 1 to NP, where NP is the number of players
    int stype = get_sentence_type(node);
    assert(stype == SENTENCE_TYPE::LEGAL || stype == SENTENCE_TYPE::DOES);
    assert(node.sub.size() > 1);
    assert(node.sub[0].type == TYPE::CONST);
    const int player_id_token = node.sub[0].value;
    if (token_to_player_id.count(player_id_token) == 0) {
        const int new_id = token_to_player_id.size() + 1;
        token_to_player_id[player_id_token] = new_id;
    }
    return token_to_player_id[player_id_token];
}


int get_or_create_sentence_id(const HighNode &node) {
    const string sentence_str = node.to_string();
    if (sentence_ids.count(sentence_str) == 0) {
        const int sentence_type = get_sentence_type(node);
        const int sentence_id = sentence_ids.size() + 1;
        sentence_ids[sentence_str] = sentence_id;
        assert((int)sentence_id_to_str.size() == sentence_id);
        sentence_id_to_str.push_back(sentence_str);
        int player_id = -1;
        if (sentence_type == SENTENCE_TYPE::DOES || sentence_type == SENTENCE_TYPE::LEGAL) {
            player_id = get_player_id(node);
        }
        assert((int)sentence_infos.size() == sentence_id);
        sentence_infos.push_back(SentenceInfo());
        int equivalent_sentence_id = -1;
        if (is_with_equivalent_type(sentence_type)) {
            HighNode equivalent;
            get_equivalent_sentence_node(node, equivalent);
            equivalent_sentence_id = get_or_create_sentence_id(equivalent);
        }
        sentence_infos[sentence_id] = SentenceInfo(
                sentence_type, player_id, equivalent_sentence_id);
    }
    return sentence_ids[sentence_str];
}

void generate_ids() {
    initialize_global_token_ids();
    prepare_value_to_theo_type_map();
    ifstream inpf(input_path);

    GDLToken token;
    string line;
    HighNode node;
    sentence_id_to_str.push_back("$NOPE$!!!");
    sentence_infos.push_back(SentenceInfo(-1));
    int done_counter = 0;
    while (getline(inpf, line)) {
        GDLTokenizer::tokenize_str(line, token);
        node.fill_from_token(token);
        for (int i = 0; i < (int)node.sub.size(); ++i) {
            HighNode &not_not_node = not_stripper(node.sub[i]);
            const int sentence_type = get_sentence_type(not_not_node);

            if (i == 0 || is_input_type(sentence_type) ||
                sentence_type == SENTENCE_TYPE::LEGAL) {
                get_or_create_sentence_id(not_not_node);
            }
        }
        ++done_counter;
        if (done_counter % 10000 == 0)
            cerr << "done lines n: " << done_counter << endl;
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

void load_theorems() {
    // removes distinct - it should be always true anyways
    sentence_datas.resize(upper_sentence_id());
    theorem_datas.resize(0);
    theorem_datas.push_back(TheoremData());
    theorem_id_to_str.resize(0);
    theorem_id_to_str.push_back("!$!!!NOPE_THEOREM!$!!!");
    ifstream inpf(input_path);
    GDLToken token;
    string line;
    int theorem_id = 1;
    while (getline(inpf, line)) {
        GDLTokenizer::tokenize_str(line, token);
        HighNode node;
        node.fill_from_token(token);
        int head_id = sentence_ids[node.sub[0].to_string()];
        if (head_id == 0) {
            cerr << node.sub[0].to_string() << endl;
        }
        assert(head_id > 0);

        theorem_datas.push_back(TheoremData());
        assert((int)theorem_datas.size() == 1 + theorem_id);
        auto &theorem_to_fill = theorem_datas.back();
        sentence_datas[head_id].is_head_of_theorem_ids.push_back(theorem_id);
        bool always_false = false;
        int forward_counter = 0;
        for (size_t i = 1; i < node.sub.size(); ++i) {
            const auto &snode = node.sub[i];
            assert(snode.value != NEXT_TOKEN_ID);
            int flag;
            const int sub_sentence_id = get_sub_sentence_id(snode, flag);
            if (flag == SUB_SENTENCE_FLAG::ALWAYS_TRUE) {
                continue; // skip sentence, because it is always true
            } else if (flag == SUB_SENTENCE_FLAG::ALWAYS_FALSE) {
                forward_counter = 1;
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
                sentence_datas[sub_sentence_id].containing_theorem_ids.push_back(mult * theorem_id);
                theorem_to_fill.right_side_sentence_ids.push_back(mult * sub_sentence_id);
            }
        }
        theorem_to_fill.head_id = head_id;
        theorem_to_fill.counter_max = forward_counter;
        theorem_to_fill.counter_value = 0;
        theorem_to_fill.always_false = always_false;
        theorem_id_to_str.push_back(line);
        ++theorem_id;
        assert((int)theorem_id_to_str.size() == theorem_id);
    }
}

void find_ids_to_remove() {
    vector<pair<int, bool>> const_sentences_queue;

    debug_always_true_sentence.resize(0);
    debug_always_true_sentence.resize(upper_sentence_id());
    debug_always_false_sentence.resize(0);
    debug_always_false_sentence.resize(upper_sentence_id());

    debug_always_true_theorem.resize(0);
    debug_always_true_theorem.resize(upper_theorem_id());
    debug_always_false_theorem.resize(0);
    debug_always_false_theorem.resize(upper_theorem_id());
    const_theos.resize(0);
    const_theos.resize(upper_theorem_id());
    const_sentences.resize(0);
    const_sentences.resize(upper_sentence_id());
    for (int sentence_i = 1; sentence_i < upper_sentence_id(); ++sentence_i) {
        sentence_datas[sentence_i].valid_is_head_of_counter = 
            sentence_datas[sentence_i].is_head_of_theorem_ids.size();
    }

    for (int theorem_id = 1; theorem_id < upper_theorem_id(); ++theorem_id) {
        const auto &theo = theorem_datas[theorem_id];
        const int sentence_id = theo.head_id;
        const int sentence_type = sentence_infos[sentence_id].type;
        if (sentence_type == SENTENCE_TYPE::INIT) {
            // skip init statements
            assert(theo.counter_max == 0);
            assert(!theo.always_false);
            continue;
        }
        // no true and does on left side of theorem
        assert(!is_input_type(sentence_type));
        if (!is_removable_type(sentence_type)) continue;

        if (theo.always_false) {
            const_theos[theorem_id] = true;
            debug_always_false_theorem[theorem_id] = true;
            int &valid_theo_counter = 
                sentence_datas[sentence_id].valid_is_head_of_counter;
            assert(valid_theo_counter > 0);
            --valid_theo_counter;
            if (valid_theo_counter == 0) {
                assert(!const_sentences[sentence_id]);
                debug_always_false_sentence[sentence_id] = true;
                const_sentences[sentence_id] = true;
                const_sentences_queue.push_back(make_pair(sentence_id, false));
            }
        }
        if (theo.counter_max == 0 && !theo.always_false) {
            const_theos[theorem_id] = true;
            debug_always_true_theorem[theorem_id] = true;
            if (!const_sentences[sentence_id]) {
                debug_always_true_sentence[sentence_id] = true;
                const_sentences[sentence_id] = true;
                const_sentences_queue.push_back(make_pair(sentence_id, true));
            }
        }
    }

    while (!const_sentences_queue.empty()) {
        const auto to_process = const_sentences_queue.back();
        const_sentences_queue.pop_back();
        const int sentence_id = to_process.first;
        const bool sentence_value = to_process.second;
        const auto &deps = sentence_datas[sentence_id].containing_theorem_ids;
        for (int theo_id: deps) {
            if (!sentence_value) {
                theo_id = -theo_id;
            }
            auto &theo = theorem_datas[abs(theo_id)];
            const int head_sentence_type = sentence_infos[theo.head_id].type;
            assert(!is_input_type(head_sentence_type));
            if (!is_removable_type(head_sentence_type)) continue;
            if (const_theos[abs(theo_id)]) {
                assert(debug_always_false_theorem[abs(theo_id)]);
                continue;
            }
            if (theo_id > 0) {
                ++theo.counter_value;
                assert(theo.counter_value <= theo.counter_max);
                if (theo.counter_value == theo.counter_max) {
                    debug_always_true_theorem[theo_id] = true;
                    debug_always_true_sentence[theo.head_id] = true;
                    const_theos[theo_id] = true;
                    const_sentences[theo.head_id] = true;
                    const_sentences_queue.push_back(make_pair(theo.head_id, true));
                }
            } else {
                assert(theo_id < 0);
                theo_id = -theo_id;
                int dep_sentence_id = theo.head_id;
                debug_always_false_theorem[theo_id] = true;
                const_theos[theo_id] = true;
                int &valid_t_counter = sentence_datas[dep_sentence_id].valid_is_head_of_counter;
                --valid_t_counter;
                assert(valid_t_counter >= 0);
                if (valid_t_counter == 0) {
                    debug_always_false_sentence[dep_sentence_id] = true;
                    assert(!const_sentences[dep_sentence_id]);
                    const_sentences[dep_sentence_id] = true;
                    const_sentences_queue.push_back(make_pair(dep_sentence_id, false));
                }
            }
        }
    }

    // remove theorems which point to always true sentences
    for (int theo_id = 1; theo_id < upper_theorem_id(); ++theo_id) {
        const int sentence_id = theorem_datas[theo_id].head_id;
        if (const_sentences[sentence_id] && !const_theos[theo_id]) {
            assert(debug_always_true_sentence[sentence_id]);
            const_theos[theo_id] = true;
        }
    }
}

void collect_and_filter_prop_net_data() {
    // remove const normal which, assert there is no always true does
    // if there is const legal, terminal, goal, init or next- leave it
    // remove distinct (because it is always true)
    cerr << "loading theorems" << endl;
    load_theorems();

    cerr << "starting propagation" << endl;
    find_ids_to_remove();
    for (int i = 1; i < (int)debug_always_true_sentence.size(); ++i) {
        assert((debug_always_true_sentence[i] || debug_always_false_sentence[i]) ==
               const_sentences[i]);
    }
    for (int i = 1; i < (int)debug_always_true_theorem.size(); ++i) {
        assert(((debug_always_true_theorem[i] || debug_always_false_theorem[i]) ==
               const_theos[i]) || debug_always_true_sentence[theorem_datas[i].head_id]);
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
        } else if (debug_always_false_theorem[i]) {
            cerr << "false: ";
        } else {
            assert(debug_always_true_sentence[theorem_datas[i].head_id]);
            cerr << "pointing to const s: ";
        }
        cerr << theorem_id_to_str[i] << "\n";
    }
    theorem_remap.resize(upper_theorem_id());
    sentence_remap.resize(upper_sentence_id());
    sentence_remap[0] = -1;
    theorem_remap[0] = -1;
    int theorem_counter = 1;
    for (size_t theo_id = 1; theo_id < theorem_remap.size(); ++theo_id) {
        if (!const_theos[theo_id]) {
            theorem_remap[theo_id] = theorem_counter++;
        } else {
            theorem_remap[theo_id] = -1;
        }
    }
    int sentence_counter = 1;
    for (size_t sentence_id = 1; sentence_id < sentence_remap.size(); ++sentence_id) {
        if (!const_sentences[sentence_id]) {
            sentence_remap[sentence_id] = sentence_counter++;
        } else {
            sentence_remap[sentence_id] = -1;
        }
    }
}


void save_debug_info() {
    ofstream debug_out(OutputPaths::debug_info);
    const int T = theorem_remap.size() - count(theorem_remap.begin(), theorem_remap.end(), -1);
    const int S = sentence_remap.size() - count(sentence_remap.begin(), sentence_remap.end(), -1);
    debug_out << "#SENTENCE_MAPPING: " << S << "\n";
    for (size_t sentence_id = 1; sentence_id < sentence_remap.size(); ++sentence_id) {
        int new_id = sentence_remap[sentence_id];
        if (new_id != -1) {
            assert(new_id > 0);
            debug_out << new_id << "\n" << sentence_id_to_str[sentence_id] << "\n";
        }
    }
    debug_out << "\n#THEOREM_MAPPING: " << T << "\n";
    for (size_t theo_id = 1; theo_id < theorem_remap.size(); ++theo_id) {
        int new_id = theorem_remap[theo_id];
        if (new_id != -1) {
            assert(new_id > 0);
            debug_out << new_id << "\n" << theorem_id_to_str[theo_id] << "\n";
        }
    }

    debug_out << "\n#REMOVED_SENTENCES:\n";
    for (size_t sentence_id = 1; sentence_id < sentence_remap.size(); ++sentence_id) {
        int new_id = sentence_remap[sentence_id];
        if (new_id == -1) {
            if (debug_always_true_sentence[sentence_id]) {
                debug_out << "always true: ";
            } else if (debug_always_false_sentence[sentence_id]) {
                debug_out << "always false: ";
            } else {
                debug_out << "pointing to const: ";
                assert(false);
            }
            debug_out << sentence_id_to_str[sentence_id] << "\n";
        }
    }
    debug_out << "\n#REMOVED_THEOREMS\n";
    for (size_t theo_id = 1; theo_id < theorem_remap.size(); ++theo_id) {
        int new_id = theorem_remap[theo_id];
        if (new_id == -1) {
            if (debug_always_true_theorem[theo_id]) {
                debug_out << "always true: ";
            } else if (debug_always_false_theorem[theo_id]) {
                debug_out << "always false: ";
            } else {
                assert(debug_always_true_sentence[theorem_datas[theo_id].head_id]);
            }
            debug_out << theorem_id_to_str[theo_id] << "\n";
        }
    }
}

void save_propnet_data() {
    // propnet data format
    // T, S - first line - number of theorems, number of sentences
    // next T lines: sentence_id, counter_max
    // next S lines: forward_deps
    //      forward dep: n_deps deps
    ofstream outfile(OutputPaths::propnet_data);
    const int T = theorem_remap.size() - count(theorem_remap.begin(), theorem_remap.end(), -1);
    const int S = sentence_remap.size() - count(sentence_remap.begin(), sentence_remap.end(), -1);
    outfile << T << " " << S << "\n";
    for (size_t theo_id = 1; theo_id < theorem_remap.size(); ++theo_id) {
        if (theorem_remap[theo_id] != -1) {
            assert(theorem_remap[theo_id] > 0);
            const auto &tc = theorem_datas[theo_id];
            int new_sentence_id = sentence_remap[tc.head_id];
            assert(new_sentence_id > 0 && new_sentence_id <= S);
            int new_counter_max = tc.counter_max - tc.counter_value;
            assert(new_counter_max >= 0);
            assert(!is_removable_type(sentence_infos[tc.head_id].type)
                   || new_counter_max > 0);
            outfile << new_sentence_id << " " << new_counter_max << "\n";
        }
    }
    for (size_t sentence_id = 1; sentence_id < sentence_remap.size(); ++sentence_id) {
        if (sentence_remap[sentence_id] != -1) {
            assert(sentence_remap[sentence_id] > 0);
            const auto &deps = sentence_datas[sentence_id].containing_theorem_ids;
            int still_valid_counter = 0;
            for (auto dep: deps) {
                if (theorem_remap[abs(dep)] > 0) {
                    ++still_valid_counter;
                }
            }
            outfile << still_valid_counter << " ";
            for (auto dep: deps) {
                int remaped = theorem_remap[abs(dep)];
                if (remaped > 0) {
                    outfile << sgn(dep) * remaped << " ";
                }
            }
            outfile << "\n";
            assert(!is_output_type(sentence_infos[sentence_id].type) || still_valid_counter == 0);
        }
    }
}

void save_backtrack_data() {
    // backtrack data format
    // S - number of sentences
    // sentence pack: number of theorems for given sentence
    //      theorem pack:
    //          theorem_id number_of_theorem_deps theorem_deps
    const int S = sentence_remap.size() - count(sentence_remap.begin(), sentence_remap.end(), -1);
    ofstream outfile(OutputPaths::backtrack_data);
    outfile << S << "\n";
    for (size_t sentence_id = 1; sentence_id < sentence_remap.size(); ++sentence_id) {
        if (sentence_remap[sentence_id] != -1) {
            assert(sentence_remap[sentence_id] > 0);
            int valid_theorem_counter = 0;
            const auto &sdata = sentence_datas[sentence_id];
            for (auto theo_id: sdata.is_head_of_theorem_ids) {
                if (theorem_remap[abs(theo_id)] > 0) ++valid_theorem_counter;
            }
            int stype = sentence_infos[sentence_id].type;
            if (!(valid_theorem_counter > 0 || !is_removable_type(stype))) {
                cerr << "wut? stype: " << stype << endl;
                cerr << sentence_id_to_str[sentence_id] << endl;
            }
            assert(valid_theorem_counter > 0 || !is_removable_type(stype));
            outfile << valid_theorem_counter << "\n";
            for (auto theo_id: sdata.is_head_of_theorem_ids) {
                const int new_theo_id = theorem_remap[abs(theo_id)];
                if (new_theo_id == -1) {
                    continue;
                }
                assert(new_theo_id > 0);
                const auto &deps = theorem_datas[theo_id].right_side_sentence_ids;
                int valid_deps_counter = 0;
                for (auto dep_sentence_id: deps) {
                    if (sentence_remap[abs(dep_sentence_id)] != -1) {
                        ++valid_deps_counter;
                    }
                }
                outfile << new_theo_id << " " << valid_deps_counter << " ";
                for (auto dep_sentence_id: deps) {
                    if (sentence_remap[abs(dep_sentence_id)] != -1) {
                        outfile << sgn(dep_sentence_id) * sentence_remap[abs(dep_sentence_id)] << " ";
                    }
                }
                outfile << "\n";
            }
        }
    }
}

void save_types_and_pairings_data() {
    // types_and_pairings data format
    // S - number of sentences
    // next S: lines - sentence_id type_id [paired_id (if NEXT, TRUE, LEGAL or DOES)] [player_id (if LEGAL or DOES)]
    ofstream outfile(OutputPaths::types_and_pairings);
    const int S = sentence_remap.size() - count(sentence_remap.begin(), sentence_remap.end(), -1);
    outfile << S << "\n";
    for (size_t sentence_id = 1; sentence_id < sentence_remap.size(); ++sentence_id) {
        const int new_id = sentence_remap[sentence_id];
        if (new_id != -1) {
            const auto &sentence_info = sentence_infos[sentence_id];
            assert(new_id > 0);
            outfile << new_id << " " << sentence_info.type << " ";
            if (sentence_info.equivalent_id != -1) {
                const int new_equiv_id = sentence_remap[sentence_info.equivalent_id];
                outfile << new_equiv_id << " ";
            } else {
                assert(!is_with_equivalent_type(sentence_info.type));
            }
            if (sentence_info.player_id != -1) {
                outfile << sentence_info.player_id;
            } else {
                assert(sentence_info.type != SENTENCE_TYPE::DOES &&
                       sentence_info.type != SENTENCE_TYPE::LEGAL);
            }
            outfile << "\n";
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 3) {
        cerr << "usage: " << argv[0] << " INPUT OUTPUT_DIR \n";
        return 1;
    }
    input_path = argv[1];
    string output_dir = string(argv[2]) + string("/");
    system(("mkdir -p " + output_dir).c_str());
    OutputPaths::debug_info = output_dir + OutputSuffix::DEBUG_INFO;
    OutputPaths::propnet_data = output_dir + OutputSuffix::PROPNET_DATA;
    OutputPaths::backtrack_data = output_dir + OutputSuffix::BACKTRACK_DATA;
    OutputPaths::types_and_pairings = output_dir + OutputSuffix::TYPES_AND_PAIRINGS;

    cerr << "COLLECTING IDS" << endl;
    generate_ids();
    collect_and_filter_prop_net_data();
    save_debug_info();
    save_propnet_data();
    save_backtrack_data();
    save_types_and_pairings_data();

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
