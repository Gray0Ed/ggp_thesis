#include <iostream>
#include <vector>
#include <algorithm>
#include <fstream>
#include <regex>
#include "GDLTokenizer.hpp"

using namespace std;
int main(int argc, char **argv) {
    smatch maach;
    regex reegex(" bla ([^[:space:]]) \1");
    regex_search("bla bo bubla bi bi bla abi abi", maach, reegex);
    cerr << "prefix: " << maach.prefix() << endl;
    for (int i = 0; i < maach.size(); ++i) {
        cerr << maach[i] << "\n";
    }
    cerr << "suffix: " << maach.suffix() << endl;
    return 0;
    if (argc < 3) {
        cerr << "usage: " << argv[0] << " INPUT OUTPUT\n";
        return 1;
    }
    vector<GDLToken> rule_tokens;
    GDLTokenizer::tokenize(argv[1], rule_tokens);
    vector<string> lines;
    for (const auto &token: rule_tokens) {
        lines.push_back(token.to_nice_string() + "\n");
    }
    sort(lines.begin(), lines.end());
    ofstream output(argv[2]);
    for (const auto &line: lines) {
        output << line;
    }
    return 0;
}
