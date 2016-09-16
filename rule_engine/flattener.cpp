#include <iostream>
#include <fstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cctype>
#include <cassert>
#include <functional>
#include <algorithm>
#include <cstring>
#include <climits>


#ifndef NO_BACKWARD
#define BACKWARD_HAS_DW 1
#include "backward.hpp"

namespace backward {
    backward::SignalHandling sh;
};

#endif

#include "MyArrays.hpp"
#include "GDLTokenizer.hpp"
#include "common.hpp"
#include "aligner.hpp"
#include "HighNode.hpp"

using namespace std;


static unordered_map<size_t, Domain*> &domain_map = globals().domain_map;

void collect_domain_types(vector<HighNode> & vhn) {
    unordered_map<size_t, unordered_set<string>> checker;
    for (HighNode &hn: vhn) {
        hn.assign_domain_hash_and_pattern(checker);
    }
    for (auto kv: checker) {
        assert(kv.second.size() < 2);
    }
}


void collect_initial_valuations(const vector<HighNode> &rules){
    for (const HighNode &hn: rules) {
        if (hn.type == TYPE::SENTENCE) {
            DomainValuation new_valuation;
            hn.gather_base_valuations_from_consts(new_valuation);
            domain_map[hn.domain_hash]->valuations.push_back(new_valuation);
        }
    }
}


void collect_alignment_infos(const vector<HighNode> &rules, vector<AlignmentInfo> &res) {
    res.resize(0);
    for (const auto &hn: rules) {
        if (hn.type == TYPE::THEOREM) {
            AlignmentInfo ai = hn.alignment_info();
            res.push_back(ai);
            // TODO remove asserts
            assert(ai.source_sentences == res.back().source_sentences);
            for (const auto &sv: ai.source_sentences) {
                assert(sv);
            }
            for (const auto &sv: res.back().source_sentences) {
                assert(sv);
            }
            //cerr << res.back().sources_new_valuations_n << endl;
            //cerr << hn.domain_pattern << endl;
            //cerr << domain_map[hn.sub[0].domain_hash].to_string();
        }
    }
}


void fill_domains(const vector<HighNode> &rules) {
    collect_initial_valuations(rules);
    vector<AlignmentInfo> alignment_infos;
    collect_alignment_infos(rules, alignment_infos);
    cerr << "starting fix point align" << endl;
    fix_point_align(alignment_infos);
}


void print_solved_theorems(const vector<HighNode> &rules, const string &outf_name) {
    unordered_set<string> printed_strings;
    ofstream output_file(outf_name);
    cerr << "printing..." << endl;
    for (auto &rule: rules) {
        string to_print;
        const auto &dom = *domain_map[rule.domain_hash]; 
        if (rule.type != TYPE::THEOREM) {
            assert(rule.type == TYPE::SENTENCE);
            to_print = "( <= " + rule.to_string() + " )\n";
        } else {
            to_print = dom.to_full_string();
        }
        if (printed_strings.count(to_print) == 0) {
            printed_strings.insert(to_print);
            output_file << to_print;
        }
    }
}


int main(int argc, char **argv) {
    if (argc < 2) {
        cerr << "Usage:\n" << argv[0] << " INPUT OUTPUT" << endl;
        return 1;
    }
    vector<GDLToken> rule_tokens;
    GDLTokenizer::tokenize(argv[1], rule_tokens);
//    for (const auto &token: rule_tokens) {
//        cerr << token.to_nice_string() + "\n";
//    }
//    cerr << "XXXX" << endl;
    vector<HighNode> rules = HighNode::generate_from_tokens(rule_tokens); 
    for (const auto &rule: rules) {
        assert(rule.type == TYPE::THEOREM);
    }
    collect_domain_types(rules);
//    cerr << rules.size() << endl;
    fill_domains(rules);
    print_solved_theorems(rules, argv[2]);
    int legal_counter = 0;
    int true_counter = 0;
    for (const auto &dit: domain_map) {
        const auto &dom = *dit.second;
        if (dom.type == DTYPE::SENTENCE) {
            if (dom.pattern.substr(0, 5) == "does ") {
                legal_counter += dom.valuations.size();
            }
            if (dom.pattern.substr(0, 5) == "true ") {
                true_counter += dom.valuations.size();
            }
        }
    }
    cerr << "LEGALS: " << legal_counter << " " << "NEXTS: " << true_counter << endl;
    for (const auto &fo: domain_map) {
        delete fo.second;
    }
    return 0;
}
