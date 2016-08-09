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

using namespace std;
string input; const int MAX_SUB_NODES = 10;
const int MAX_DOMAIN_VARS = 10;

hash<string> str_hasher;

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

template <typename T>
struct LimitedArray {
    T *items;
    bool on_stack;
    size_t size, max_sz;

    LimitedArray() {
        size = 0;
        on_stack = false;
        items = 0;
    }

    LimitedArray(size_t limit) {
        max_sz = limit;
        items = new T[max_sz];
        size = 0;
        on_stack = false;
    }

    LimitedArray(size_t limit, T* area) {
        items = area;
        on_stack = true;
        size = 0;
        max_sz = limit;
    }

    ~LimitedArray() {
        if (!on_stack) {
            delete [] items;
        }
    }

    LimitedArray(const LimitedArray<T> &la) {
        size = la.size;
        for (int i = 0; i < size; ++i) items[i] = la.items[i];
    }

    LimitedArray<T> &operator=(const LimitedArray<T> &la) {
        size = la.size;
        for (int i = 0; i < size; ++i) items[i] = la.items[i];
        return *this;
    }

    T &operator[](int i) {
        assert(size >= 0);
        assert(size <= max_sz);
        assert(i < size && i >= 0);
        return items[i];
    }

    T operator[](int i) const {
        assert(size >= 0);
        assert(size <= max_sz);
        assert(i < size && i >= 0);
        return items[i];
    }

    void append(const T& t) {
        assert(size < max_sz);
        items[size++] = t;
    }

    T &back(int i) {
        return items[size - 1 - i];
    }

    T back(int i) const {
        return items[size - 1 - i];
    }
};

namespace TYPE {
    enum {
        VAR,
        CONST,
        THEOREM,
        SENTENCE,
    };
};

struct Domain {
    size_t id; // hash of the pattern
    string pattern;
    vector<unordered_set<string>> var_dom;
    Domain(){}
    Domain(string _pattern) {
        pattern = _pattern;
        id = str_hasher(pattern);
        var_dom.resize(count(pattern.begin(), pattern.end(), '#'));
    }

    string to_string() {
        string res = pattern + "\n";
        for (auto & q: var_dom) {
            for (auto &r: q) {
                res += " " + r;
            }
            res += "\n";
        }
        return res;
    }
};

unordered_map<size_t, Domain> domain_map;

struct HighNode {
    int type;
    int n_theorem_vars;
    size_t domain_hash;
    string domain_pattern;
    string value;
    int nvalue;
    Token debug_token;
    vector<HighNode> sub;
    vector<vector<unordered_set<string>*>> equivalence_sets;

    void fill_from_token(const Token &t, 
            unordered_map<string, int> &var_mapping) {
        debug_token = t;
        if (t.leaf()) {
            assert(!t.val.empty());
            if (t.val[0] == '?') {
                type = TYPE::VAR;
                if (var_mapping.count(t.val) == 0) {
                    int sz = var_mapping.size();
                    var_mapping[t.val] = sz; 
                }
                nvalue = var_mapping[t.val];
            } else {
                type = TYPE::CONST;
                value = t.val;
            }
        } else if (t(0) == "<=") {
            assert(t.sub.size() >= 3);
            type = TYPE::THEOREM;
            sub.resize(t.sub.size() - 1);
            for (int i = 1; i < t.sub.size(); ++i) {
                sub[i - 1].fill_from_token(t.sub[i], var_mapping);
                if (i == 1) {
                    n_theorem_vars = var_mapping.size();
                }
            }
        } else {
            type = TYPE::SENTENCE;
            assert(!t.sub.empty());
            assert(t(0) != "");
            assert(t.sub[0].leaf());
            value = t(0);
            sub.resize(t.sub.size() - 1);
            for (int i = 1; i < t.sub.size(); ++i) {
                sub[i - 1].fill_from_token(t.sub[i], var_mapping);
            }
        }
    }

    static vector<HighNode> generate_from_root(const Token &root) {
        vector<HighNode> res;
        res.resize(root.sub.size());
        for (int i = 0; i < root.sub.size(); ++i) {
            unordered_map<string, int> var_mapping;
            res[i].fill_from_token(root.sub[i], var_mapping);
        }
        return res;
    }

    string assign_domain_hash_and_pattern(unordered_map<size_t, unordered_set<string>> & checker) {
        string res = value;
        if (res == "next") {
            res = "true";
        }
        if (res == "legal") {
            res = "does";
        }
        for (HighNode &hn: sub) {
            if (type == TYPE::THEOREM) {
                hn.assign_domain_hash_and_pattern(checker);
            }
            else if (hn.type == TYPE::VAR || hn.type == TYPE::CONST) {
                res += " #";
            } else if (hn.type == TYPE::SENTENCE) {
                res += " ( " + hn.assign_domain_hash_and_pattern(checker) + " )";
            } else {
                assert(0);
            }
        }
        if (type != TYPE::THEOREM) {
            domain_pattern = res;
            domain_hash = str_hasher(res);
            domain_map[domain_hash] = Domain(domain_pattern);
            checker[domain_hash] = unordered_set<string>();
            checker[domain_hash].insert(domain_pattern);
            assert(domain_map[domain_hash].id == domain_hash);
        }
        assert(res.find("next") == string::npos && res.find("legal") == string::npos);
        return res;
    }

    void gather_domain_base_from_consts() {
        if (type == TYPE::THEOREM) {
            for (HighNode &hn: sub) {
                hn.gather_domain_base_from_consts();
            }
        } else if (type == TYPE::SENTENCE) {
            auto &var_dom = domain_map[domain_hash].var_dom;
            int arg_counter = 0;
            for (HighNode &hn: sub) {
                if (hn.type == TYPE::CONST) {
                    assert(arg_counter < var_dom.size());
                    var_dom[arg_counter].insert(hn.value);
                    arg_counter++;
                } else if (hn.type == TYPE::VAR) {
                    ++arg_counter;
                } else if (hn.type == TYPE::SENTENCE) {
                    hn.gather_domain_base_from_consts();
                    const Domain &sub_d = domain_map[hn.domain_hash];
                    for (int i = 0; i < sub_d.var_dom.size(); ++i) {
                        assert(arg_counter < var_dom.size());
                        var_dom[arg_counter].insert(
                                sub_d.var_dom[i].begin(),
                                sub_d.var_dom[i].end());
                        ++arg_counter;
                    }
                } else {
                    assert(0);
                }
            }
        }
    }

    int domains_intersect(LimitedArray<unordered_set<string>> & var_intersect,
                           LimitedArray<bool> & intersect_started) {
        if (type == TYPE::SENTENCE && (value == "not" || value == "distinct")) {
            return 0;
        }
        int counter = 0;
        for (int i = 0; i < sub.size(); ++i) {
            if (sub[i].type == TYPE::VAR) {
                int n = sub[i].nvalue;
                auto & domain_set = domain_map[domain_hash].var_dom[counter];
                auto & cur_domain_set = var_intersect[n];
                ++counter;
                if (!intersect_started[n]) {
                    intersect_started[n] = true;
                    cur_domain_set = domain_set;
                } else {
                    string _stacked_data[cur_domain_set.size()];
                    LimitedArray<string> to_remove(cur_domain_set.size(), _stacked_data);

                    for (const auto &q: var_intersect[n]) {
                        if (domain_set.count(q) == 0) {
                            to_remove.append(q);
                        }
                    }
                    for (int i = 0; i < to_remove.size; ++i) {
                        cur_domain_set.erase(to_remove[i]);
                    }
                }
            } else if (sub[i].type != TYPE::CONST) {
                counter += sub[i].domains_intersect(var_intersect, intersect_started);
            } else {
                ++counter;
            }
        }
        return counter;
    }

    int domains_union(LimitedArray<unordered_set<string>> & var_intersect) {
        int counter = 0;
        for (int i = 0; i < sub.size(); ++i) {
            if (sub[i].type == TYPE::VAR) {
                domain_map[domain_hash].var_dom[counter].insert(
                    var_intersect[sub[i].nvalue].begin(),
                    var_intersect[sub[i].nvalue].end());
                ++counter;
            } else if (sub[i].type != TYPE::CONST) {
                counter += sub[i].domains_union(var_intersect);
            } else {
                ++counter;
            }
        }
        return counter;
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
        hn.gather_domain_base_from_consts();
        if (hn.type == TYPE::THEOREM) {
            max_th_vars = max(max_th_vars, hn.n_theorem_vars);
        }
    }

    bool changed = true;
    LimitedArray<unordered_set<string>> var_intersect(max_th_vars);
    LimitedArray<bool> intersect_started(max_th_vars);
    while (changed) {
        changed = false;
        for (HighNode &hn: vhn) {
            if (hn.type == TYPE::THEOREM) {
                var_intersect.size = hn.n_theorem_vars;
                intersect_started.size = hn.n_theorem_vars;
                for (int i = 0; i < var_intersect.size; ++i) {
                    var_intersect[i].clear();
                    memset(intersect_started.items, 0, sizeof(bool) * intersect_started.size);
                }
                for (int i = 1; i < hn.sub.size(); ++i) {
                    hn.sub[i].domains_intersect(var_intersect, intersect_started);
                }
                changed = changed || hn.sub[0].domains_union(var_intersect);
            }
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
