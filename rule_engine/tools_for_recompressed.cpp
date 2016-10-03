#include "tools_for_recompressed.hpp"

static int _identity_mapper(int x) {
    return x;
}

function<int(int)> identity_mapper = _identity_mapper;

function<int(int)> consensus_mapper_generator(
        const unordered_map<string, int> &a, const vector<string> &b) {
    cerr << "computing consensus: " << a.size() << " " << b.size() << endl;
    vector<int> consensus;
    assert(a.size() == b.size() - 1);
    consensus.resize(b.size());
    for (int it = 1; it < (int)b.size(); ++it) {
        consensus[it] = a.at(b[it]);
    }
    return [=](int x) -> int {
        assert(x > 0 && x < (int)consensus.size());
        return consensus[x];
    };
}

void load_sentence_infos(
        const string &input_path, function<int(int)> mapper, vector<SentenceInfo> &sentence_infos) {
    ifstream inf(input_path);
    if (!inf) {
        throw runtime_error("file: " + input_path + " does not exist.");
    }
    int n_sentences;
    inf >> n_sentences;
    sentence_infos.resize(0);
    sentence_infos.resize(n_sentences + 1);
    for (int it = 1; it <= n_sentences; ++it) {
        int sentence_id;
        inf >> sentence_id;
        sentence_id = mapper(sentence_id);
        assert(sentence_id > 0 && sentence_id <= n_sentences);
        SentenceInfo &to_fill = sentence_infos[sentence_id];
        assert(to_fill.type == -1);
        inf >> to_fill.type;
        if (is_with_equivalent_type(to_fill.type)) {
            inf >> to_fill.equivalent_id;
        } else {
            to_fill.equivalent_id = -1;
        }
        if (is_with_player_type(to_fill.type)) {
            inf >> to_fill.player_id;
        } else {
            to_fill.player_id = -1;
        }
    }
}
