#include <iostream>
#include <vector>
#include <algorithm>
#include <fstream>
#include <regex>
#include <unordered_set>
#include "GDLTokenizer.hpp"

#ifndef NO_BACKWARD
#define BACKWARD_HAS_DW 1
#include "backward.hpp"

namespace backward {
    backward::SignalHandling sh;
};

#endif


using namespace std;
int main(int argc, char **argv) {
    smatch reg_mach;
    regex reg_exp(" distinct ([^[:space:]]+) \\1");
    if (argc < 3) {
        cerr << "usage: " << argv[0] << " INPUT OUTPUT\n";
        return 1;
    }
    vector<GDLToken> rule_tokens;
    cerr << "before tokenize" << endl;
    GDLTokenizer::tokenize(argv[1], rule_tokens);
    cerr << "after tokenize" << endl;
    vector<string> lines;
    unordered_set<string> already_printed;
    for (const auto &token: rule_tokens) {
        string nice_string = token.to_nice_string();
        if (nice_string.find("base") != string::npos) continue;
        if (nice_string.find("input") != string::npos) continue;
        // warning - it will produce wrong output if there is something like not (distinct X X)
        if (regex_search(nice_string, reg_mach, reg_exp) // remove distinct X X
                || already_printed.count(nice_string) > 0) {
            continue;
        }
        already_printed.insert(nice_string);
        lines.push_back(nice_string + "\n");
    }
    sort(lines.begin(), lines.end());
    ofstream output(argv[2]);
    for (const auto &line: lines) {
        output << line;
    }
    return 0;
}
