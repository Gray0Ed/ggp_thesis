#pragma once
#include <vector>
#include <cctype>
#include <fstream>
#include <cassert>
#include <iostream>

using namespace std;

struct GDLToken {
    string val;
    vector<GDLToken> sub;

    string to_string(int ntabs=0) const {
        string res = val + ":\n";
        for (const GDLToken & t: sub) {
            res += t.to_string(ntabs + 1);
        }
        res.insert(0, ntabs, ' ');
        return res;
    }

    string to_nice_string(bool is_top=true) const {
        string res = val;
        if (!sub.empty()) {
            assert(res == "");
            res = "(";
        }
        for (const auto &subt: sub) {
            res += " " + subt.to_nice_string(false);
        }
        if (!sub.empty()) {
            res += " )";
        }
        if (is_top && sub.size() == 0) {
            cerr << val << endl;
        }
        assert(!is_top || sub.size() > 0);
        if (is_top && sub[0].val != "<=") {
            return "( <= " + res + " )"; // every top level rules should be
                                         // presented as theorem
        }
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

    string operator()(size_t i) const {
        assert(sub.size() >= 0);
        assert(i < sub.size() && i >= 0);
        return sub[i].val;
    }

    void shorten_edges() {
        for (GDLToken &t : sub) {
            t.shorten_edges();
        }
        if (sub.size() == 1) {
            GDLToken new_me = sub[0];
            this->val = new_me.val;
            this->sub = new_me.sub;
        }
    }
};

struct GDLTokenizer {
    string input;
    bool is_whitespace(char c) {
        return isspace(c);
    }

    bool is_name_char(char c) {
        return !is_whitespace(c) && c != '(' && c != ')';
    }

    size_t tokenize(size_t c, GDLToken &to_fill) {
        struct AfterPrint {
            size_t to_print;
            ~AfterPrint() {
                cerr << to_print << "\n";
            }
            AfterPrint(size_t _tp) {
                to_print = _tp;
            }
        };
        //AfterPrint ap(c);
        //cerr << c << "\n";

        while (true) {
            if (input.size() == c) return c;
            assert(input.size() > c);
            char cur = input[c];
            if (cur == '(') {
                to_fill.sub.push_back(GDLToken());
                c = tokenize(c + 1, to_fill.sub.back());
                continue;
            } else if (cur == ')') {
                return c + 1;
            } else if (is_whitespace(cur)) {
                c += 1;
            } else {
                size_t s = c;
                while (c < input.size() && is_name_char(input[c])) {
                    ++c;
                }
                to_fill.sub.push_back(GDLToken());
                to_fill.sub.back().val = input.substr(s, c - s);
            }
        }
        assert(0);
    }

    static void tokenize(const string &input_path, vector<GDLToken> &result) {
        ifstream inp(input_path);
        string input = string((istreambuf_iterator<char>(inp)), istreambuf_iterator<char>());
        GDLToken root;
        tokenize_str(input, root);
        result = root.sub;
    }
    
    static void tokenize_str(const string &input, GDLToken &result) {
        GDLTokenizer gdl_tokenizer;
        gdl_tokenizer.input = input;
        result.sub.resize(0);
        result.val = "";
        assert(gdl_tokenizer.tokenize(0, result) == gdl_tokenizer.input.size());
        result.shorten_edges();
    }
};
