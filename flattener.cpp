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
#include <array>
#include <climits>

using namespace std;
string input;
const int MAX_DOMAIN_VARS = 20;

hash<string> str_hasher;
typedef array<short, MAX_DOMAIN_VARS> DomainValuation;

unordered_map<string, int> numeric_rename;
vector<string> reverse_numeric_rename;

struct Token {
    string val;
    vector<Token> sub;

    string to_string(int ntabs=0) const {
        string res = val + ":\n";
        for (const Token & t: sub) {
            res += t.to_string(ntabs + 1);
        }
        res.insert(0, ntabs, ' ');
        return res;
    }

    bool leaf() const {
        return sub.empty();
    }

    //string &operator()(int i) {
    //    assert(sub.size() >= 0);
    //    assert(i < sub.size() && i >= 0);
    //    return sub[i].val;
    //}

    string operator()(int i) const {
        assert(sub.size() >= 0);
        assert(i < sub.size() && i >= 0);
        return sub[i].val;
    }

    void shorten_edges() {
        for (Token &t : sub) {
            t.shorten_edges();
        }
        if (sub.size() == 1) {
            *this = sub[0];
        }
    }
};


bool is_whitespace(char c) {
    return isspace(c);
}

bool is_name_char(char c) {
    return !is_whitespace(c) && c != '(' && c != ')';
}

int _tokenize(int c, Token &to_fill) {
    if (input.size() == c) return c;
    char cur = input[c];
    if (cur == '(') {
        to_fill.sub.push_back(Token());
        return _tokenize(_tokenize(c + 1, to_fill.sub.back()), to_fill);
    } else if (cur == ')') {
        return c + 1;
    } else if (is_whitespace(cur)) {
        return _tokenize(c + 1, to_fill);
    } else {
        int s = c;
        while (c < input.size() && is_name_char(input[c])) {
            ++c;
        }
        to_fill.sub.push_back(Token());
        to_fill.sub.back().val = input.substr(s, c - s);
        return _tokenize(c, to_fill);
    }
}

void tokenize(Token &root) {
    assert(_tokenize(0, root) == input.size());
    root.shorten_edges();
}

namespace TYPE {
    enum {
        NONE,
        VAR,
        CONST,
        THEOREM,
        SENTENCE,
    };
};

namespace DTYPE {
    enum {
        SENTENCE,
        THEOREM
    };
};


struct Domain {
    size_t id; // hash of the pattern
    int type; // 
    string pattern;
    vector<DomainValuation> valuations;
    int valuation_size;
    Domain(){}
    Domain(string _pattern, int _type) {
        type = _type;
        pattern = _pattern;
        id = str_hasher(pattern);
        valuation_size = count(pattern.begin(), pattern.end(), '#');
        assert(valuation_size <= MAX_DOMAIN_VARS);
    }

    string to_string() {
        string res = pattern + "\n";
        for (auto &dv: valuations) {
            for (int i = 0; i < valuation_size; ++i) {
                res += " " + reverse_numeric_rename[dv[i]];
            }
            res += "\n";
        }
        return res;
    }
};
unordered_map<size_t, Domain> domain_map;

int rename(const string &token) {
    if (numeric_rename.count(token) == 0) {
        int s = numeric_rename.size();
        numeric_rename[token] = s;
        reverse_numeric_rename.push_back(token);
        assert(reverse_numeric_rename.size() == s + 1);
        assert(s <= SHRT_MAX);
    }
    return numeric_rename[token];
}

struct HighNode {
    int type;
    int n_theorem_vars;
    size_t domain_hash;
    string domain_pattern;
    int value;
    int exp_var_id;
    Token debug_token;
    vector<HighNode> sub;
    vector<vector<unordered_set<string>*>> equivalence_sets;

    bool is_complex_const() const {
        return type == TYPE::CONST && sub.size() > 0;
    }
    
    bool is_simple_const() const {
        return type == TYPE::CONST && !is_complex_const();
    }

    bool is_simple_sentence() const {
        return type == TYPE::SENTENCE && sub.size() == 0;
    }

    void fill_from_token(const Token &t, 
            unordered_map<int, int> &var_mapping,
            int induced_type=TYPE::NONE) {
        debug_token = t;
        if (t.leaf()) {
            assert(!t.val.empty());
            int renamed = rename(t.val);
            if (induced_type == TYPE::CONST) {
                if (t.val[0] == '?') {
                    type = TYPE::VAR;
                    if (var_mapping.count(renamed) == 0) {
                        int sz = var_mapping.size();
                        var_mapping[renamed] = sz; 
                    }
                    exp_var_id = var_mapping[renamed];
                } else {
                    type = TYPE::CONST;
                    value = renamed;
                }
            } else {
                assert(induced_type == TYPE::SENTENCE);
                assert(t.val[0] != '?');
                type = TYPE::SENTENCE;
                value = renamed;
            }
        } else if (t(0) == "<=") {
            assert(t.sub.size() >= 3);
            assert(induced_type == TYPE::NONE);
            type = TYPE::THEOREM;
            sub.resize(t.sub.size() - 1);
            for (int i = 1; i < t.sub.size(); ++i) {
                sub[i - 1].fill_from_token(t.sub[i], var_mapping, TYPE::SENTENCE);
                if (i == 1) {
                    n_theorem_vars = var_mapping.size();
                }
            }
        } else {
            if (induced_type == TYPE::CONST) {
                type = TYPE::CONST;
            } else {
                assert(induced_type == TYPE::SENTENCE || induced_type == TYPE::NONE);
                type = TYPE::SENTENCE;
            }
            assert(!t.sub.empty());
            assert(t(0) != "");
            assert(t.sub[0].leaf());
            value = rename(t(0));
            sub.resize(t.sub.size() - 1);
            for (int i = 1; i < t.sub.size(); ++i) {
                sub[i - 1].fill_from_token(t.sub[i], var_mapping, TYPE::CONST);
            }
        }
        assert(type != TYPE::NONE);
    }

    static vector<HighNode> generate_from_root(const Token &root) {
        vector<HighNode> res;
        res.resize(root.sub.size());
        for (int i = 0; i < root.sub.size(); ++i) {
            unordered_map<int, int> var_mapping;
            res[i].fill_from_token(root.sub[i], var_mapping);
        }
        return res;
    }

    string assign_domain_hash_and_pattern(unordered_map<size_t, unordered_set<string>> & checker) {
        string res;
        if (type != TYPE::THEOREM) {
            res = reverse_numeric_rename[value];
        }
        if (res == "next" || res == "init") {
            res = "true";
        }
        if (res == "legal") {
            res = "does";
        }
        bool first_done = false;
        for (HighNode &hn: sub) {
            if (hn.type == TYPE::VAR || hn.is_simple_const()) {
                res += " #";
            } else if (hn.type == TYPE::SENTENCE || hn.is_complex_const()) {
                res += " ( " + hn.assign_domain_hash_and_pattern(checker) + " )";
            } else {
                cerr << debug_token.to_string() << endl;
                cerr << hn.type << " " << hn.debug_token.to_string() << endl;
                assert(0);
            }
            if (type == TYPE::THEOREM && !first_done) {
                first_done = true;
                assert(hn.type == TYPE::SENTENCE);
                res += " <=";
            }
        }
        assert(type == TYPE::THEOREM || type == TYPE::SENTENCE || is_complex_const());
        if (!is_complex_const()) {
            domain_pattern = res;
            domain_hash = str_hasher(res);
            int domain_type;
            if (type == TYPE::THEOREM) {
                domain_type = DTYPE::THEOREM;
            } else {
                domain_type = DTYPE::SENTENCE;
            }
            domain_map[domain_hash] = Domain(domain_pattern, domain_type);
            if (checker.count(domain_hash) == 0) {
                checker[domain_hash] = unordered_set<string>();
            }
            checker[domain_hash].insert(domain_pattern);
            assert(domain_map[domain_hash].id == domain_hash);
        }
        assert(res.find("next") == string::npos && 
               res.find("legal") == string::npos && res.find("init") == string::npos);
        return res;
    }

    void gather_base_valuations_from_consts(DomainValuation &to_fill, int &index) {
        for (HighNode &hn: sub) {
            assert(hn.type == TYPE::CONST);
            if (hn.is_simple_const()) {
                to_fill[index++] = hn.value;
            } else {
                hn.gather_base_valuations_from_consts(to_fill, index);
            }
        }
    }
};

void collect_domain_types(vector<HighNode> & vhn) {
    unordered_map<size_t, unordered_set<string>> checker;
    for (HighNode &hn: vhn) {
        hn.assign_domain_hash_and_pattern(checker);
    }
    for (auto kv: checker) {
        assert(kv.second.size() < 2);
    }
}

void fill_domains(vector<HighNode> & vhn) {
    int max_th_vars = 0;
    for (HighNode &hn: vhn) {
        if (hn.type == TYPE::SENTENCE) {
            DomainValuation new_valuation;
            int index = 0;
            hn.gather_base_valuations_from_consts(new_valuation, index);
            domain_map[hn.domain_hash].valuations.push_back(new_valuation);
        }
    }
}


int main(int argc, char **argv) {
    if (argc < 2) {
        cerr << "no input provided" << endl;
        return 1;
    }
    ifstream inp(argv[1]);
    input = string((istreambuf_iterator<char>(inp)),
            istreambuf_iterator<char>());
    Token root;
    tokenize(root);
//    root.shorten_edges();
    cerr << root.to_string() << endl;
    vector<HighNode> vhn = HighNode::generate_from_root(root); 
    collect_domain_types(vhn);
//    for (auto & hn: vhn) {
//        cerr << hn.domain_pattern << endl;
//    }
    fill_domains(vhn);
    for (auto & dm: domain_map) {
        cerr << dm.second.to_string();
    }
    return 0;
}
