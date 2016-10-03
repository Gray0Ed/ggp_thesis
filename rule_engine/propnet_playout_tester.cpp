#include <iostream>
#include <fstream>
#include <cassert>
#include <unordered_set>
#include <algorithm>

#ifndef NO_BACKWARD
#define BACKWARD_HAS_DW 1
#include "backward.hpp"

namespace backward {
    backward::SignalHandling sh;
};

#endif

#include "propnet.hpp"
#include "tools_for_recompressed.hpp"
#include "recompressor.hpp"
#include "GDLTokenizer.hpp"

using namespace std;


struct TruthKeeper {
    unordered_set<int> are_true;
    void update(const vector<int> &update_delta) {
        for (int id: update_delta) {
            if (id > 0) {
                are_true.insert(id);
            } else if (are_true.count(-id) > 0) {
                are_true.erase(id);
            }
        }
    }
};

DebugInfo debug_info;
vector<SentenceInfo> sentence_infos;
vector<vector<int>> delta_states, delta_inputs;
vector<int> initial_input;  // all sentences listed in init should be set to true

void split_by_dollar(const string &s, vector<string> &output) {
    output.resize(0);
    int last_i = 0;
    for (int i = 0; i < (int)s.size(); ++i) {
        if (s[i] == '$') {
            if (last_i != i) {
                output.push_back(s.substr(last_i, i - last_i));
            }
            last_i = i + 1;
        }
    }
}

void strings_to_ids(const vector<string> &strings, vector<int> &output) {
    output.resize(0);
    GDLToken tok;
    for (const auto &sentence_str: strings) {
        GDLTokenizer::tokenize_str(sentence_str, tok);
        assert(debug_info.sentence_ids.count(tok.to_nice_string()) > 0);
        output.push_back(debug_info.sentence_ids[tok.to_nice_string()]);
        assert(output.back() > 0);
    }
    sort(output.begin(), output.end());
}

vector<int> true_into_next(const vector<int> &differential) {
    vector<int> res;
    res.resize(differential.size());
    for (int i = 0; i < (int)differential.size(); ++i) {
        const int sentence_id = differential[i];
        const auto &sinfo = sentence_infos[abs(sentence_id)];
        if (sinfo.type == SENTENCE_TYPE::TRUE) {
            assert(sinfo.equivalent_id != -1);
            res[i] = sgn(sentence_id) * sinfo.equivalent_id;
        } 
    }
    return res;
}

vector<int> strip_legal(const vector<int> &state) {
    vector<int> res;
    for (int sentence_id: state) {
        if (sentence_infos[sentence_id].type != SENTENCE_TYPE::LEGAL) {
            res.push_back(sentence_id);
        }
    }
    return res;
}

vector<int> state_differential(vector<int> &last, vector<int> &current) {
    int last_i = 0, current_i = 0;
    vector<int> result;
    while (last_i < (int)last.size() || current_i < (int)current.size()) {
        if (last_i < (int)last.size()) assert(last[last_i] > 0);
        if (current_i < (int)current.size()) assert(current[current_i] > 0);
        if (last_i == (int)last.size()) {
            result.push_back(current[current_i++]);
        } else if (current_i == (int)current.size()) {
            result.push_back(-last[last_i++]);
        } else if (last[last_i] < current[current_i]) {
            result.push_back(-last[last_i++]);
        } else if (last[last_i] > current[current_i]) {
            result.push_back(current[current_i++]);
        } else {
            assert(last[last_i] == current[current_i]);
            ++last_i;
            ++current_i;
        }
        if (result.size()) {
            assert(result.back() != 0);
        }
    }
    return result;
}

void load_recompressed(const string &recompressed_path) {
    debug_info.load(recompressed_path + "/" + OutputSuffix::DEBUG_INFO);
    load_sentence_infos(
        recompressed_path + "/" + OutputSuffix::TYPES_AND_PAIRINGS, 
        identity_mapper,
        sentence_infos
    );

    initial_input.resize(0);
    for (int sentence_id = 1; sentence_id < (int)sentence_infos.size(); ++sentence_id) {
        const auto &sinfo = sentence_infos[sentence_id];
        if (sinfo.type == SENTENCE_TYPE::INIT) {
            initial_input.push_back(sinfo.equivalent_id);
        }
    }
}

void load_test_data(const string &test_file_path) {
    delta_states.resize(0);
    delta_inputs.resize(0);
    ifstream inputf(test_file_path);
    if (!inputf) {
        throw runtime_error("file: " + test_file_path + " does not exist.");
    }
    string line;
    vector<string> splitted;
    const int TRUE_SENTENCES = 0;
    const int DONE_MOVES = 1;
    int reading_state = TRUE_SENTENCES;
    vector<int> last_state, state, last_input, input, input_helper;
    last_input = initial_input;
    while (getline(inputf, line)) {
        split_by_dollar(line, splitted);
        if (reading_state == TRUE_SENTENCES) {
            cerr << " reading state \n";
            strings_to_ids(splitted, state);
            delta_states.push_back(true_into_next(state_differential(last_state, state)));
            last_state = state;
        } else {
            cerr << " reading input \n";
            assert(reading_state == DONE_MOVES);
            input = strip_legal(state);
            strings_to_ids(splitted, input_helper);
            input.insert(input.end(), input_helper.begin(), input_helper.end());
            delta_inputs.push_back(state_differential(last_input, input));
            last_input = input;
        }
        reading_state = (reading_state + 1) % 2;
    }
    cerr << "hmm: " << delta_states.size() << " " << delta_inputs.size() << endl;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        cerr << "usage: " << argv[0] << " INPUT_FILE RECOMPRESSED_PROPNET_PATH" << endl;
        return 0;
    }
    string test_file_path = argv[1];
    string recompressed_propnet_path = argv[2];
    Propnet propnet;
    propnet.load(recompressed_propnet_path);
    load_recompressed(recompressed_propnet_path);
    load_test_data(test_file_path);
    assert(delta_states.size() == delta_inputs.size() + 1);
    propnet.reset();
    vector<int> delta_output;
    propnet.run(initial_input, delta_output);
    propnet.list_all_true_outputs(delta_output);

    TruthKeeper source_tk, propnet_tk;
    source_tk.update(delta_states[0]);
    propnet_tk.update(delta_output);
    assert(source_tk.are_true == propnet_tk.are_true);
    for (int i = 0; i < (int)delta_inputs.size(); ++i) {
        propnet.run(delta_inputs[i], delta_output);
        propnet_tk.update(delta_output);
        source_tk.update(delta_states[i + 1]);
        assert(propnet_tk.are_true == source_tk.are_true);
    }
    return 0;
}
