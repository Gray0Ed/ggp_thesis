#pragma once

#include <cassert>

#include <functional>
#include <algorithm>
#include <vector>
#include <stdexcept>

using namespace std;

#include "GDLTokenizer.hpp"
#include "recompressor.hpp"
#include "common.hpp"

void load_sentence_infos(const string &input_path, function<int(int)> mapper,
                         vector<SentenceInfo> &sentence_infos);

struct BacktrackData {
    struct SentenceHook {
        int offset; // index of first data member representing given sentence
        int n_theorems; // number of theorems for given sentence
        SentenceHook() {
            offset = -1;
        }
    };
    vector<int> data;
    vector<SentenceHook> sentence_offsets; 
    int max_sentence_id() {
        return sentence_offsets.size() - 1;
    }

    bool operator==(const BacktrackData &bd) const {
        if (sentence_offsets.size() != bd.sentence_offsets.size()) {
            return false;
        }
        unordered_map<int, int> theo_off[2];
        const vector<int> *datas[2];
        datas[0] = &data;
        datas[1] = &bd.data;
        for (int sentence_id = 1; sentence_id < (int)sentence_offsets.size(); ++sentence_id) {
            const auto &sa = sentence_offsets[sentence_id];
            const auto &sb = bd.sentence_offsets[sentence_id];
            if (sa.n_theorems != sb.n_theorems) {
                return false;
            }
            theo_off[0].clear();
            theo_off[1].clear();
            int current_offset[2];
            current_offset[0] = sa.offset;
            current_offset[1] = sb.offset;
            for (int tit = 0; tit < sa.n_theorems; ++tit) {
                for (int i = 0; i < 2; ++i) {
                    int theo_id = (*datas[i])[current_offset[i]++];
                    theo_off[i][theo_id] = current_offset[i];
                    int n_deps = (*datas[i])[current_offset[i]++];
                    current_offset[i] += n_deps;
                }
            }
            if (theo_off[0].size() != theo_off[1].size()) {
                return false;
            }
            for (const auto &kv: theo_off[0]) {
                if (theo_off[1].count(kv.first) != 1) return false;
                int offset1 = kv.second;
                int offset2 = theo_off[1][kv.first];
                int sz = (*datas[0])[offset1];
                if (sz != (*datas[1])[offset2]) return false;
                for (int i = 1; i <= sz; ++i) {
                    if ((*datas[0])[offset1 + i] != (*datas[1])[offset2 + i]) return false;
                }
            }
        }
        return true;
    }

    void load(const string &input_path, function<int(int)> smapper, function<int(int)> tmapper) {
        data.resize(0);
        sentence_offsets.resize(0);
        ifstream inp(input_path);
        if (!inp) {
            throw runtime_error("file: " + input_path + " does not exist.");
        }
        int n_sentences;
        inp >> n_sentences;
        sentence_offsets.resize(n_sentences + 1);
        for (int it = 1; it <= n_sentences; ++it) {
            const int sentence_id = smapper(it);
            assert(sentence_id > 0 && sentence_id <= n_sentences);
            auto &to_fill = sentence_offsets[sentence_id];
            assert(to_fill.offset == -1);
            to_fill.offset = data.size();
            inp >> to_fill.n_theorems;
            for (int tit = 0; tit < to_fill.n_theorems; ++tit) {
                int theorem_id, n_theo_deps;
                inp >> theorem_id >> n_theo_deps;
                theorem_id = tmapper(theorem_id);
                data.push_back(theorem_id);
                data.push_back(n_theo_deps);
                int first_dep_offset = data.size();
                for (int tdit = 0; tdit < n_theo_deps; ++tdit) {
                    int dep_id;
                    inp >> dep_id;
                    int abs_dep_id = smapper(abs(dep_id));
                    dep_id = sgn(dep_id) * abs_dep_id;

                    assert(abs_dep_id > 0 && abs_dep_id <= n_sentences);
                    data.push_back(dep_id);
                }
                if ((int)data.size() != first_dep_offset) {
                    sort(&data[0] + first_dep_offset, &data[0] + data.size());
                }
            }
        }
    }
};


struct PropnetData {
    // TODO: remember to prepare TheoremHook counter values run "ALL FALSE" first propagation

    struct GateCounter {
        int counter_max;
        int true_counter;
        int false_counter;

        bool is_saturated() const {
            return true_counter + false_counter == counter_max;
        }

        bool partially_is_valid() const {
            return true_counter >= 0 && true_counter <= counter_max && 
                   false_counter >= 0 && false_counter <= counter_max;
        }

        bool is_valid() const {
            return is_saturated() && partially_is_valid();
        }

        void increment() {
            ++true_counter;
            --false_counter;
        }

        void decrement() {
            ++false_counter;
            --true_counter;
        }

        bool all_true() const {
            return true_counter == counter_max;
        }

        bool any_true() const {
            return true_counter > 0;
        }

        bool all_false() const {
            return false_counter == counter_max;
        }

        bool any_false() const {
            return false_counter > 0;
        }
    };

    struct TheoremHook: GateCounter {
        int sentence_id;
        TheoremHook() {
            sentence_id = -1;
            counter_max = -1;
            true_counter = -1;
            false_counter = -1;
        }
    };

    struct SentenceHook: GateCounter {
        int offset;
        int n_deps;
        int value; // -1 - undecided, 0 - false, 1 - true;
        SentenceHook() {
            offset = -1;
            n_deps = -1;
            false_counter = -1;
            true_counter = -1;
            counter_max = 0;
            value = -2;
        }
    };

    static const int UNDECIDED = -1;
    static const int POSITIVE = 1;
    static const int NEGATIVE = 0;

    vector<TheoremHook> theorem_hooks;
    vector<SentenceHook> sentence_hooks;
    vector<int> deps_data;

    bool operator==(const PropnetData &pd) const {
        if (pd.theorem_hooks.size() != theorem_hooks.size() ||
            pd.sentence_hooks.size() != sentence_hooks.size()) {
            return false;
        }
        for (int theo_id = 1; theo_id < (int)theorem_hooks.size(); ++theo_id) {
            if (theorem_hooks[theo_id].sentence_id != pd.theorem_hooks[theo_id].sentence_id || 
                theorem_hooks[theo_id].counter_max != pd.theorem_hooks[theo_id].counter_max) {
                return false;
            }
        }
        for (int sentence_id = 1; sentence_id < (int)sentence_hooks.size(); ++sentence_id) {
            const auto &shook1 = sentence_hooks[sentence_id];
            const auto &shook2 = pd.sentence_hooks[sentence_id];
            if (shook1.n_deps != shook2.n_deps) {
                return false;
            }
            for (int i = 0; i < shook1.n_deps; ++i) {
                if (deps_data[shook1.offset + i] != pd.deps_data[shook2.offset + i]) {
                    return false;
                }
            }
        }
        return true;
    }

    void load(const string &input_path, function<int(int)> smapper, function<int(int)>tmapper) {
        theorem_hooks.resize(0);
        deps_data.resize(0);
        int n_sentences, n_theorems;
        ifstream inp(input_path);
        if (!inp) {
            throw runtime_error("file: " + input_path + " does not exist.");
        }
        inp >> n_theorems >> n_sentences;
        theorem_hooks.resize(n_theorems + 1);
        sentence_hooks.resize(n_sentences + 1);
        for (int it = 1; it <= n_theorems; ++it) {
            int theorem_id = tmapper(it); 
            assert(theorem_id > 0 && theorem_id <= n_theorems);
            auto &to_fill = theorem_hooks[theorem_id];
            assert(to_fill.sentence_id == -1);
            int sentence_id;
            inp >> sentence_id;
            sentence_id = smapper(sentence_id);
            assert(sentence_id > 0 && sentence_id <= n_sentences);
            to_fill.sentence_id = sentence_id;
            inp >> to_fill.counter_max;
            ++sentence_hooks[sentence_id].counter_max;
        }
        for (int it = 1; it <= n_sentences; ++it) {
            int sentence_id = smapper(it);
            assert(sentence_id > 0 && sentence_id <= n_sentences);
            auto &to_fill = sentence_hooks[sentence_id];
            assert(to_fill.offset == -1);
            to_fill.offset = deps_data.size();
            inp >> to_fill.n_deps;
            for (int dit = 0; dit < to_fill.n_deps; ++dit) {
                int dep;
                inp >> dep;
                int abs_dep = tmapper(abs(dep));
                assert(abs_dep > 0 && abs_dep <= n_theorems);
                dep = sgn(dep) * abs_dep;
                deps_data.push_back(dep);
            }
            if ((int)deps_data.size() != to_fill.offset) {
                sort(&deps_data[0] + to_fill.offset, 
                     &deps_data[0] + to_fill.offset + to_fill.n_deps);
            }
        }
    }
};


struct DebugInfo {
    unordered_map<string, int> sentence_ids, theorem_ids;
    vector<string> sentence_id_to_str, theorem_id_to_str;

    void load(const string &input_path) {
        sentence_ids.clear();
        theorem_ids.clear();
        sentence_id_to_str.resize(0);
        theorem_id_to_str.resize(0);
        ifstream inp(input_path);
        if (!inp) {
            throw runtime_error("file: " + input_path + " does not exist.");
        }
        const int INIT = 0;
        const int SENTENCE_R = 1;
        const int THEOREM_R = 2;
        int mode = INIT;
        bool id_was_read = false;
        int id, n_sentences, n_theorems;
        string line;
        GDLToken token;
        const string SMAPPING_HEADER = "#SENTENCE_MAPPING:";
        const string TMAPPING_HEADER = "#THEOREM_MAPPING:";
        const string REMOVED_S_HEADER = "#REMOVED_SENTENCES:";
        while (getline(inp, line)) {
            if (all_of(line.begin(), line.end(), [](char c){return isspace(c);})) continue;
            if (mode == INIT && line.find(SMAPPING_HEADER) != string::npos) {
                mode = SENTENCE_R;
                n_sentences = stoi(line.substr(SMAPPING_HEADER.size()));
                sentence_id_to_str.resize(n_sentences + 1);
            } else if (mode == SENTENCE_R && line.find(TMAPPING_HEADER) != string::npos) {
                mode = THEOREM_R;
                n_theorems = stoi(line.substr(TMAPPING_HEADER.size()));
                theorem_id_to_str.resize(n_theorems + 1);
            } else if (mode == THEOREM_R && line.find(REMOVED_S_HEADER) != string::npos) {
                break;
            } else {
                if (!id_was_read) {
                    id = stoi(line);
                    assert(id > 0);
                    id_was_read = true;
                } else {
                    GDLTokenizer::tokenize_str(line, token);
                    const string tok_str = token.to_nice_string();
                    id_was_read = false;
                    unordered_map<string, int> *to_fill = 0;
                    vector<string> *reverse_to_fill = 0;
                    if (mode == SENTENCE_R) {
                        to_fill = &sentence_ids;
                        reverse_to_fill = &sentence_id_to_str;
                    } else if (mode == THEOREM_R) {
                        to_fill = &theorem_ids;
                        reverse_to_fill = &theorem_id_to_str;
                    } else {
                        assert(0);
                    }
                    assert(to_fill->count(tok_str) == 0);
                    assert((int)(*reverse_to_fill).size() > id);
                    assert((*reverse_to_fill)[id] == "");
                    (*to_fill)[tok_str] = id;
                    (*reverse_to_fill)[id] = tok_str;
                }
            }
        }
    }
};

function<int(int)> consensus_mapper_generator(
        const unordered_map<string, int> &a, const vector<string> &b);

extern function<int(int)> identity_mapper;
