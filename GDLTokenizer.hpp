#include <vector>
#include <cctype>
#include <fstream>

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

    string to_nice_string() const {
        string res = val;
        if (!sub.empty()) {
            assert(res == "");
            res = "(";
        }
        for (const auto &subt: sub) {
            res += " " + subt.to_nice_string();
        }
        if (!sub.empty()) {
            res += " )";
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

    string operator()(int i) const {
        assert(sub.size() >= 0);
        assert(i < sub.size() && i >= 0);
        return sub[i].val;
    }

    void shorten_edges() {
        for (GDLToken &t : sub) {
            t.shorten_edges();
        }
        if (sub.size() == 1) {
            *this = sub[0];
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

    int tokenize(int c, GDLToken &to_fill) {
        if (input.size() == c) return c;
        char cur = input[c];
        if (cur == '(') {
            to_fill.sub.push_back(GDLToken());
            return tokenize(tokenize(c + 1, to_fill.sub.back()), to_fill);
        } else if (cur == ')') {
            return c + 1;
        } else if (is_whitespace(cur)) {
            return tokenize(c + 1, to_fill);
        } else {
            int s = c;
            while (c < input.size() && is_name_char(input[c])) {
                ++c;
            }
            to_fill.sub.push_back(GDLToken());
            to_fill.sub.back().val = input.substr(s, c - s);
            return tokenize(c, to_fill);
        }
    }

    static void tokenize(const string &input_path, vector<GDLToken> &result) {
        GDLTokenizer gdl_tokenizer;
        ifstream inp(input_path);
        gdl_tokenizer.input = string((istreambuf_iterator<char>(inp)), istreambuf_iterator<char>());
        GDLToken root;
        assert(gdl_tokenizer.tokenize(0, root) == gdl_tokenizer.input.size());
        root.shorten_edges();
        for (const auto &rule_token: root.sub) {
            result.push_back(rule_token);
        }
    }
};