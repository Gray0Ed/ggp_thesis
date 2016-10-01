#pragma once
#include <vector>
using namespace std;

#include "tools_for_recompressed.hpp"

struct Propnet: private PropnetData {
    vector<SentenceInfo> sentence_infos;

    void load(const string &dir);
    void reset();

    // list of positive id if true, negative if flase, included only if changed from last time
    void run(const vector<int> &delta_input, 
             vector<int> &delta_output);
private:
    bool operator==(const Propnet &p) const { return false;}
};
