#include <iostream>
#include <queue>
#include <unordered_map>

using namespace std;

#include "propnet.hpp"

struct pair_hash {
    inline size_t operator()(const std::pair<int, int> &v) const {
        return v.first * 31 + v.second;
    }
};

void Propnet::load(const string &dir) {
    PropnetData::load(dir + '/' + OutputSuffix::PROPNET_DATA, identity_mapper, identity_mapper);
    load_sentence_infos(dir + '/' + OutputSuffix::TYPES_AND_PAIRINGS, identity_mapper, sentence_infos);
    di.load(dir + '/' + OutputSuffix::DEBUG_INFO);
}

void Propnet::reset() {
    queue<int> propagation_queue;
    vector<bool> was_visited_theo;
    vector<bool> was_visited_sen;
    was_visited_theo.resize(theorem_hooks.size());
    was_visited_sen.resize(sentence_hooks.size());
    
    for (int sentence_id = 1; sentence_id < (int)sentence_hooks.size(); ++sentence_id) {
        auto &shook = sentence_hooks[sentence_id];
        shook.false_counter = 0;
        shook.true_counter = 0;
        shook.value = UNDECIDED;
        if (sentence_id == 73) cerr << shook.counter_max << endl;
        if (is_input_type(sentence_infos[sentence_id].type)) {
            assert(shook.counter_max == 0);
            propagation_queue.push(sentence_id);
            shook.value = NEGATIVE;
        } else {
            assert(shook.counter_max > 0);
        }
    }

    for (int theorem_id = 1; theorem_id < (int)theorem_hooks.size(); ++theorem_id) {
        if (theorem_hooks[theorem_id].counter_max == 0) {
            const int sentence_id = theorem_hooks[theorem_id].sentence_id;
            assert(sentence_infos[sentence_id].type == SENTENCE_TYPE::INIT);
        }
    }

    for (int theorem_id = 1; theorem_id < (int)theorem_hooks.size(); ++theorem_id) {
        theorem_hooks[theorem_id].true_counter = 0;
        theorem_hooks[theorem_id].false_counter = 0;
    }

    while (!propagation_queue.empty()) {
        const int sentence_id = propagation_queue.front();
        propagation_queue.pop();
        const bool first_visit_sen = !was_visited_sen[sentence_id];
        was_visited_sen[sentence_id] = true;
        const auto &shook = sentence_hooks[sentence_id];
        assert(shook.value == POSITIVE || shook.value == NEGATIVE);
        const int new_value = shook.value;

        for (int depit = shook.offset; depit < shook.n_deps + shook.offset; ++depit) {
            const int dep_theo_id = deps_data[depit];
            const int theo_id = abs(dep_theo_id);
            const bool first_visit_theo = !was_visited_theo[theo_id];
            was_visited_theo[theo_id] = true;
            auto &thook = theorem_hooks[theo_id];
            auto &sub_shook = sentence_hooks[thook.sentence_id];
            bool reduce = (dep_theo_id < 0 && new_value == POSITIVE) || 
                          (dep_theo_id > 0 && new_value == NEGATIVE);

            assert(thook.partially_is_valid());
            assert(sub_shook.partially_is_valid());
            if (reduce) {
                const bool th_changed = thook.false_counter == 0;
                if (first_visit_sen) {
                    ++thook.false_counter;
                } else {
                    thook.decrement();
                }
                if (th_changed) {
                    if (first_visit_theo) {
                        ++sub_shook.false_counter;
                    } else {
                        sub_shook.decrement();
                    }
                    if (sub_shook.all_false()) {
                        sub_shook.value = NEGATIVE;
                        propagation_queue.push(thook.sentence_id);
                    }
                }
            } else {
                if (first_visit_sen) {
                    ++thook.true_counter;
                } else {
                    thook.increment();
                }

                if (thook.all_true()) {
                    const bool sub_shook_was_false = !sub_shook.any_true();
                    if (first_visit_theo) {
                        ++sub_shook.true_counter;
                    } else {
                        sub_shook.increment();
                    }
                    if (sub_shook.any_true() && sub_shook_was_false) {
                        sub_shook.value = POSITIVE;
                        propagation_queue.push(thook.sentence_id);
                    }
                } else if (first_visit_theo) {
                    ++sub_shook.false_counter;
                    if (sub_shook.all_false()) {
                        sub_shook.value = NEGATIVE;
                        propagation_queue.push(thook.sentence_id);
                    }
                }
            }
            assert(thook.partially_is_valid());
            assert(sub_shook.partially_is_valid());
        }
    }

    for (int sentence_id = 1; sentence_id < (int)sentence_hooks.size(); ++sentence_id) {
        const auto &shook = sentence_hooks[sentence_id];
        bool is_init = sentence_infos[sentence_id].type == SENTENCE_TYPE::INIT;
        assert(is_init || shook.value != UNDECIDED);
        assert(is_init || shook.is_valid());
    }
}

void Propnet::run(const vector<int> &delta_input, vector<int> &delta_output) {
    delta_output.resize(0);
    static queue<int> propagation_queue;
    static unordered_map<int, int> output_values;
    assert(propagation_queue.empty());
    output_values.clear();
    for (int sentence_id: delta_input) {
        int new_value;
        if (sentence_id > 0) {
            new_value = POSITIVE;
        } else if (sentence_id < 0) {
            new_value = NEGATIVE;
            sentence_id = -sentence_id;
        } else {
            assert(0);
        }
        if (sentence_hooks[sentence_id].value != new_value) {
            assert(is_input_type(sentence_infos[sentence_id].type));
            sentence_hooks[sentence_id].value = new_value;
            propagation_queue.push(sentence_id);
        }
    }

    while (!propagation_queue.empty()) {
        const int sentence_id = propagation_queue.front();
        propagation_queue.pop();
        const auto &shook = sentence_hooks[sentence_id];
        assert(shook.value == POSITIVE || shook.value == NEGATIVE);
        assert(shook.is_valid());
        const int new_value = shook.value;
        const int stype = sentence_infos[sentence_id].type;
        if (is_output_type(stype) || stype == SENTENCE_TYPE::LEGAL) {
            assert(stype == SENTENCE_TYPE::LEGAL || shook.n_deps == 0);
            output_values[sentence_id] = new_value;
        }

        for (int depit = shook.offset; depit < shook.n_deps + shook.offset; ++depit) {
            const int theo_id = deps_data[depit];
            auto &thook = theorem_hooks[abs(theo_id)];
            auto &sub_shook = sentence_hooks[thook.sentence_id];
            bool reduce = (theo_id < 0 && new_value == POSITIVE) || 
                          (theo_id > 0 && new_value == NEGATIVE);
            assert(sub_shook.is_valid());
            assert(thook.is_valid());
            if (reduce) {
                const bool th_was_true = thook.all_true();
                thook.decrement();
                if (th_was_true) {
                    sub_shook.decrement();
                    assert(sub_shook.value == POSITIVE);
                    if (sub_shook.all_false()) {
                        sub_shook.value = NEGATIVE;
                        propagation_queue.push(thook.sentence_id);
                    }
                }
            } else {
                thook.increment();
                if (thook.all_true()) {
                    const bool sub_shook_was_false = sub_shook.all_false();
                    sub_shook.increment();
                    if (sub_shook_was_false) {
                        assert(sub_shook.value == NEGATIVE);
                        sub_shook.value = POSITIVE;
                        propagation_queue.push(thook.sentence_id);
                    }
                }
            }
            assert(sub_shook.is_valid());
            assert(thook.is_valid());
        }
    }
    for (const auto &kv: output_values) {
        const int sentence_id = kv.first;
        const int value = kv.second;
        int mul = 1;
        if (value == NEGATIVE) {
            mul = -1;
        }
        delta_output.push_back(mul * sentence_id);
    }
}

void Propnet::list_all_true_outputs(vector<int> &output) {
    output.resize(0);
    for (int sentence_id = 1; sentence_id < (int)sentence_infos.size(); ++sentence_id) {
        const int stype = sentence_infos[sentence_id].type;
        const auto &shook = sentence_hooks[sentence_id];
        if ((stype == SENTENCE_TYPE::LEGAL || is_output_type(stype)) && shook.any_true()) {
            output.push_back(sentence_id);
        }
    }
}

