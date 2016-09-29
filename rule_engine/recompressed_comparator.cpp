#include <iostream>
#include <fstream>
#include <cassert>


#ifndef NO_BACKWARD
#define BACKWARD_HAS_DW 1
#include "backward.hpp"

namespace backward {
    backward::SignalHandling sh;
};
#endif


using namespace std;

#include "tools_for_recompressed.hpp"


int main(int argc, char **argv) {
    if (argc < 3) {
        cerr << "usage: " << argv[0] << " DIR1 DIR2\n";
        return 1;
    }
    string inpf1 = argv[1];
    string inpf2 = argv[2];
    DebugInfo di1, di2;
    di1.load(inpf1 + "/debug_info");
    di2.load(inpf2 + "/debug_info");
    auto smapper2_to_1 = consensus_mapper_generator(
            di1.sentence_ids, di2.sentence_id_to_str);
    auto tmapper2_to_1 = consensus_mapper_generator(
            di2.theorem_ids, di2.theorem_id_to_str);
    vector<SentenceInfo> sentence_infos1, sentence_infos2;
    load_sentence_infos(inpf2 + "/types_and_pairings", smapper2_to_1, sentence_infos2);
    load_sentence_infos(inpf1 + "/types_and_pairings", identity_mapper, sentence_infos1);
    assert(sentence_infos1 == sentence_infos2);

    BacktrackData bd1, bd2;
    bd1.load(inpf1 + "/backtrack_data", identity_mapper, identity_mapper);
    bd2.load(inpf2 + "/backtrack_data", smapper2_to_1, tmapper2_to_1);
    assert(bd1 == bd2);

    PropnetData pd1, pd2;
    pd1.load(inpf1 + "/propnet_data", identity_mapper, identity_mapper);
    pd2.load(inpf2 + "/propnet_data", smapper2_to_1, tmapper2_to_1);
    assert(pd1 == pd2);

    return 0;
}
