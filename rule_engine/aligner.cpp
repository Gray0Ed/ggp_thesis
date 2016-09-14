#include "aligner.hpp"
#include <iostream>

static _Aligner ali;

template<typename T>
static void uniquefy(vector<T> &v) {
    sort(v.begin(), v.end());
    auto last = unique(v.begin(), v.end());
    v.erase(last, v.end());
}

void fix_point_align(vector<AlignmentInfo> &to_align) {
   int theorem_valuations_found = 0;
   int sentence_valuations_found = 0;
   while ("Elvis Lives") {
       size_t to_be_processed_index = 0;
       for (size_t i = 0; i < to_align.size(); ++i) {
           if (to_align[i].sources_new_valuations_n > 
               to_align[to_be_processed_index].sources_new_valuations_n) {
               to_be_processed_index = i;
           }
       }
       if (to_align[to_be_processed_index].sources_new_valuations_n == 0) {
           break;
       }
       AlignmentInfo &to_be_processed = to_align[to_be_processed_index];

       Domain &sentence = *to_be_processed.destination_sentence;
       Domain &theorem = *to_be_processed.destination_theorem;
       cerr << "doing: " << theorem.pattern << endl;

       ali.find_valuations(&to_be_processed);
       cerr << "valuations found: " << ali.new_valuations.size() << endl;
       auto &tv = theorem.valuations;
       int old_tvaluations_n = tv.size();
       tv.insert(tv.end(), 
            ali.new_valuations.begin(), ali.new_valuations.end());
       uniquefy(tv);
       theorem_valuations_found += tv.size() - old_tvaluations_n;
       auto &sv = sentence.valuations;
       int old_svaluations_n = sv.size();
       for (auto &new_valuation: ali.new_valuations) {
           new_valuation.resize(sentence.valuation_size);
           sv.push_back(new_valuation);
       }
       uniquefy(sv);
       to_be_processed.sources_new_valuations_n = 0;
       int svaluations_n_delta = sv.size() - old_svaluations_n;
       sentence_valuations_found += svaluations_n_delta;
       //cerr << "new valuations n: " << valuations_n_delta << endl;
       if (sentence_valuations_found % 100 == 0) cerr << "sv: " << sentence_valuations_found << endl;
       if (theorem_valuations_found % 100 == 0)  cerr << "tv: " << theorem_valuations_found << endl;
      // cerr << "resulting theorem valuations: \n" << theorem.to_full_string() << endl;
       //cerr << "resulting domain valuations: \n" << sentence.to_full_string() << endl;
       for (auto &ai: to_align) {
           if (ai.source_sentences.contains(&sentence)) {
               ai.sources_new_valuations_n += svaluations_n_delta;
           }
       }
   }
}

bool _Aligner::prepare_indices() {
    indices.resize(sentences_n());
    indices_memory_bank.grow();
    assert(indices_memory_bank.size == 1);
    for (int sentence_i = 0; sentence_i < sentences_n(); ++sentence_i) {
        int valuation_index = 0;
        auto &sindices = indices[sentence_i];
        const auto &svequivalence = ai->var_equivalence[sentence_i];

        sindices.set_items(&indices_memory_bank.back(), 0);
        for (const auto &valuation: (*sources_valuations[sentence_i])) {
            assert(svequivalence.size == valuation.size);
            bool bad = false;
            for (const auto &var_constraint: ai->source_constraints[sentence_i]) {
                if (valuation[var_constraint.index] != var_constraint.value) {
                    bad = true;
                    break;
                }
            }
            for (size_t v_i = 0; v_i < valuation.size; ++v_i) {
                if (valuation[v_i] != valuation[svequivalence[v_i]]) {
                    bad = true;
                    break;
                }
            }
            if (!bad) {
                indices_memory_bank.grow();
                sindices[sindices.size++] = valuation_index;
            }
            ++valuation_index;
        }
        if (sindices.size == 0) {
            return false;
        }
    }
    return true;
}

void _Aligner::split_by_var(int split_by_var_id) {
    const auto &occurences = ai->var_infos[split_by_var_id].key_occurences;
    const auto &banned_values = banned_var_values[split_by_var_id];
    const IndexBound input_bounds = bounds_stack.back();
    bounds_stack.pop();
    assert(occurences.size > 0);
    for (const auto &occurence: occurences) {
        const auto &bound = input_bounds[occurence.sentence];
        auto &sindices = indices[occurence.sentence];
        assert(sindices.size > 0);
        assert(bound.first < bound.second);
        auto &valuation_set = *sources_valuations[occurence.sentence];
        sort(&sindices[0] + bound.first, &sindices[0] + bound.second, 
            [&valuation_set, &occurence](const auto &a, const auto &b) -> bool {
                return valuation_set[a][occurence.index] < valuation_set[b][occurence.index];
            }
        );
    }
    LimitedArray<int, MAX_SENTENCES_IN_THEOREM> processed_index;
    for (int i = 0; i < sentences_n(); ++i) {
        processed_index.append(input_bounds[i].first);
    }
    const auto &moccurence = occurences[0];
    const auto &mbound = input_bounds[moccurence.sentence];
    auto &mindices = indices[moccurence.sentence];
    auto &mvaluation_set = *sources_valuations[moccurence.sentence];
    auto &mindex = processed_index[moccurence.sentence];
    for (int i = 0; i < sentences_n(); ++i) {
        assert((size_t)input_bounds[i].second <= indices[i].size);
    }
    while (mindex < mbound.second) {
        const int value = 
            mvaluation_set[mindices[mindex]][moccurence.index];
        if (banned_values.contains(value)) {
            while (mindex < mbound.second && 
                    mvaluation_set[mindices[mindex]][moccurence.index] == value) {
                ++mindex;
            }
            continue;
        }
        bool bad = false;
        bounds_stack.grow();
        IndexBound &ib_to_fill = bounds_stack.back();
        ib_to_fill.resize(sentences_n());
        for (auto &ib: ib_to_fill) {
            ib.first = -1;
            ib.second = -1;
        }
        for (const auto &occurence: occurences) {
            int &pi = processed_index[occurence.sentence];
            const auto &bound = input_bounds[occurence.sentence];
            assert(bound.first != bound.second);
            assert((size_t)bound.second <= indices[occurence.sentence].size);
            auto &sindices = indices[occurence.sentence];
            auto &valuation_set = *sources_valuations[occurence.sentence];
            while (pi < bound.second && valuation_set[sindices[pi]][occurence.index] < value) ++pi;
            auto sub_bound = make_pair(pi, pi);
            //cerr << "hello again sJ\n" << occurence.index << " " << valuation_set[sindices[pi]].size << endl;
            //cerr << bound.second << " " << valuation_set.size() << " " << sindices.size << endl;
            while (pi < bound.second && valuation_set[sindices[pi]][occurence.index] == value) ++pi;
            sub_bound.second = pi;
            if (sub_bound.second == sub_bound.first) {
                bad = true;
                break;
            }
            ib_to_fill[occurence.sentence] = sub_bound;
            assert(valuation_set[sindices[sub_bound.first]][occurence.index] == valuation_set[sindices[sub_bound.second - 1]][occurence.index]);
            assert(sub_bound.first >= bound.first && sub_bound.second <= bound.second);
        }
        if (bad) {
            bounds_stack.pop();
        } else {
            for (int sentence_i = 0; sentence_i < sentences_n(); ++sentence_i) {
                if (ib_to_fill[sentence_i].first == -1) {
                    ib_to_fill[sentence_i] = input_bounds[sentence_i];
                }
                assert(ib_to_fill[sentence_i].first >= 0 && ib_to_fill[sentence_i].second >= 0);
                assert((size_t)ib_to_fill[sentence_i].second <= indices[sentence_i].size);
            }
        }
    }
}

void _Aligner::initialize_banned_var_values() {
    banned_var_values.resize(0);
    for (const auto &vi: ai->var_infos) {
        banned_var_values.append(vi.different_than_const);
    }
}

void _Aligner::ban_by_var(int var_id) {
    const auto &oc = ai->var_infos[var_id].occurences[0];
    const auto &bound = bounds_stack.back()[oc.sentence];
    assert(bound.first < bound.second);
    const int value = sources_valuations[oc.sentence]->at(
            indices[oc.sentence][bound.first])[oc.index];
    for (int dvar_id: ai->var_infos[var_id].different_than) {
        banned_var_values[dvar_id].append(value);
    }
}

void _Aligner::unban(int var_id) {
    for (int dvar_id: ai->var_infos[var_id].different_than) {
        banned_var_values[dvar_id].pop();
    }
}

void _Aligner::const_only_filler() {
    DomainValuation new_valuation;
    for (int vi: ai->domain_filling_pattern) {
        assert(vi < 0);
        new_valuation.append(-vi - 1);
    }
    new_valuations.push_back(new_valuation);
}

void _Aligner::compute() {
    if (sentences_n() == 0) {
        const_only_filler();
        return;
    }
    if (!prepare_indices()) {
        return;
    }
    if (vars_n() == 0) { // can be false for 0 vars, so prepare_indices has to run first
        const_only_filler();
        return;
    }

    initialize_banned_var_values();

    bounds_stack.resize(1);
    for (int i = 0; i < sentences_n(); ++i) {
        bounds_stack[0].append(make_pair(0, (int)indices[i].size));
    }
    //print_bounds_stack();
    split_by_var(ai->binding_order[0]);
    LimitedArray<int, MAX_DOMAIN_VARS> level_size;
    level_size.append(bounds_stack.size);
    //cerr << "boom" << endl;
    //print_bounds_stack();

    while ("Elvis Lives") {
        //cerr << "baam" << endl;
        while (level_size.size > 0 && 
               level_size.back() == 0) {
            level_size.pop();
            const int level_id = level_size.size - 1;
            if (level_id >= 0) {
                unban(ai->binding_order[level_id]);
            }
        }
        if (level_size.size == 0) break;
        //print_bounds_stack();
        const int level_id = level_size.size - 1;
        assert(level_size.back() > 0);
        --level_size.back();
        if (level_id == vars_n() - 1) {
            DomainValuation new_valuation;
            for (int vi: ai->domain_filling_pattern) {
                if (vi > 0) {
                    --vi;
                    const auto &oc = ai->var_infos[vi].occurences[0];
                   // cerr << ai.var_infos[vi].occurences[0].sentence << endl;
     //               cerr << vi << endl;
     //               cerr << oc.sentence << endl;
     //               cerr << "XOO: " << oc.index << " " << ai.var_infos[vi].occurences.size << endl;
                    const auto &ib = bounds_stack.back()[oc.sentence];
                    if (ib.first + 1 != ib.second) {
                        cerr << vars_n() << " " << sentences_n() << " " << level_id << endl;
                        for (const auto &ko: bounds_stack.back()) {
                            cerr << ko.first << "/" << ko.second << " ";
                        }
                        cerr << endl;
                        for (int iit = ib.first; iit < ib.second; ++iit) {
                            const auto &va =sources_valuations[oc.sentence]->at(
                                    indices[oc.sentence][iit]);
                            for (const auto &vo: va) {
                                cerr << vo << " ";
                            }
                            cerr << endl;
                        }
                        for (const auto &vi: ai->var_infos) {
                            for (const auto &oc: vi.occurences) {
                                cerr << oc.sentence << "/" << oc.index << " ";
                            }
                            cerr << endl;
                        }
                        cerr << endl;
                        cerr << bounds_stack.size << endl;
                        print_bounds_stack();
                    }
                    assert(ib.first + 1 == ib.second);
                    new_valuation.append(
                        sources_valuations[oc.sentence]->at(
                            indices[oc.sentence][ib.first]
                        )[oc.index]
                    );
                } else if (vi < 0) {
                    new_valuation.append(-vi - 1);
                } else {
                    assert(0);
                }
            }
            new_valuations.push_back(new_valuation);
            bounds_stack.pop();
        } else {
            //cerr << "buum" << endl;
            ban_by_var(ai->binding_order[level_id]);
            auto last = bounds_stack.back();
            size_t base = bounds_stack.size - 1;
            split_by_var(ai->binding_order[level_id + 1]);
            if (level_id + 1 == vars_n() - 1) {
                for (size_t bid = base; bid < bounds_stack.size; ++bid) {
                    for (const auto &bo: bounds_stack[bid]) {
                        if (bo.first != bo.second - 1) {
                            for (int vi: ai->domain_filling_pattern) {
                                cerr << vi << " ";
                            }
                            cerr << endl;
                            for (int bi = bo.first; bi < bo.second; ++bi) {
                                const auto &va = sources_valuations[0]->at(indices[0][bi]);
                                for (const auto &val: va) {
                                    cerr << val << " ";
                                }
                                cerr << endl;
                            }
                            cerr << endl;
                            for (const auto &lo: last) {
                                cerr << lo.first << '/' << lo.second << " ";
                            }
                            cerr << endl;
                            for (const auto &ko: ai->binding_order) {
                                cerr << ko << " ";
                            }
                            cerr << endl;
                        }
                        assert(bo.first == bo.second - 1);
                    }
                }
            }
            level_size.append(bounds_stack.size - base);
        }
    }
}

void _Aligner::print_bounds_stack() {
    for (const auto &bo: bounds_stack) {
        for (const auto &p: bo) {
            cerr << p.first << "/" << p.second << " ";
        }
        cerr << "\n";
    }
    cerr << endl;
}
