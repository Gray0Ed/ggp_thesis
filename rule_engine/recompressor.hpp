#pragma once

namespace SENTENCE_TYPE {
    enum {
        NORMAL = 0,
        DOES,
        TRUE,
        NEXT,
        LEGAL,
        TERMINAL,
        GOAL,
        INIT,
        N_SENTENCE_TYPES
    };
};


struct SentenceInfo {
    int type, equivalent_id, player_id;
    SentenceInfo() {
        type = -1;
        equivalent_id = -1;
        player_id = -1;
    }
    SentenceInfo(int _type, int _player_id=-1, int _equivalent_id=-1) {
        type = _type;
        equivalent_id = _equivalent_id;
        player_id = _player_id;
    }

    bool operator==(const SentenceInfo &si) const {
        return type == si.type && equivalent_id == si.equivalent_id && player_id == si.player_id;
    }
    // add: (or in separate structure?)
    // forward (propnet) deps
    // backtrack deps
};

inline bool is_input_type(int sentence_type) {
    // can't be on left side of any theorem 
    return sentence_type == SENTENCE_TYPE::TRUE || sentence_type == SENTENCE_TYPE::DOES;
}

inline bool is_output_type(int sentence_type) {
    // can't be on right side of any theorem
    return 
        sentence_type == SENTENCE_TYPE::NEXT ||
        sentence_type == SENTENCE_TYPE::TERMINAL ||
        sentence_type == SENTENCE_TYPE::GOAL;
}

inline bool is_removable_type(int sentence_type) {
    return sentence_type == SENTENCE_TYPE::NORMAL;
}

inline bool is_with_equivalent_type(int sentence_type) {
    return sentence_type != SENTENCE_TYPE::NORMAL &&
           sentence_type != SENTENCE_TYPE::TERMINAL &&
           sentence_type != SENTENCE_TYPE::GOAL;
}

inline bool is_with_player_type(int sentence_type) {
    return sentence_type == SENTENCE_TYPE::LEGAL ||
           sentence_type == SENTENCE_TYPE::DOES;
}
