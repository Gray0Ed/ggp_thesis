#include <iostream>
#include <cassert>

#ifndef NO_BACKWARD
#define BACKWARD_HAS_DW 1
#include "backward.hpp"

namespace backward {
    backward::SignalHandling sh;
};

#endif

#include "propnet.hpp"

using namespace std;

int main(int argc, char **argv) {
    if (argc < 2) {
        cerr << "usage: " << argv[0] << " INPUT_FILE RECOMPRESSED_PROPNET_PATH" << endl;
    }
    string test_file_path = argv[1];
    string recompressed_propnet_path = argv[2];
    Propnet propnet;
    propnet.load(recompressed_propnet_path);
    vector<vector<int>> delta_states;
    vector<vector<int>> delta_inputs;
    load_test_data(delta_states, delta_inputs);
    assert(delta_states.size() == delta_inputs.size());
    propnet.reset();
    vector<int> delta_output;
    for (int i = 0; i < (int)delta_inputs.size(); ++i) {
        propnet.run(delta_inputs[i], delta_output);
        assert(delta_output == delta_states[i]);
        // zle bo delta output to moze byc nadzbior
    }
    return 0;
}
