#include "ai_abi.h"

#include <iostream>
#include <random>

static std::random_device dev;

static std::mt19937 rng(dev());

static std::uniform_int_distribution<> dist(0, 6);

extern "C" {
/**
 * Initialize the personal datastore for the AI
 * The implementation for this function is completely
 * optional !
*/
void init(void **data)
{

}
}

static int get_winning_move(board_t *board)
{
    for (int x = 0; x < 7; x++) {
        if (!is_legal_move(board, x))
            continue;
        place_piece(board, x, PLAYER_O);
        if (check_win(board, PLAYER_O, "AI", false)) {
            remove_piece(board, x, PLAYER_O);
            return x;
        }
        remove_piece(board, x, PLAYER_O);
    }
    return -1;
}

static uint8_t get_non_losing_moves(board_t *board)
{
    uint8_t res = 0b01111111;
    for (int x = 0; x < 7; x++) {
        if (!is_legal_move(board, x))
            continue;
        place_piece(board, x, PLAYER_O);
        for (int y = 0; y < 7; y++) {
            if (!is_legal_move(board, y))
                continue;
            place_piece(board, y, PLAYER_X);
            if (check_win(board, PLAYER_X, NULL, false)) {
                res &= 0b11111111 & (0 << x);
                remove_piece(board, y, PLAYER_X);
                break;
            }
            remove_piece(board, y, PLAYER_X);
        }
        remove_piece(board, x, PLAYER_O);
    }
    return res;
}

static int get_non_losing_move(board_t *board)
{
    uint8_t bitset = get_non_losing_moves(board);
    int res = 0;

    if (!bitset) {
        for (int i = 0; i < 7; i++) {
            if (is_legal_move(board, i))
                return i;
        }
        abort();
    }
    do {
        res = dist(rng);
    } while (!is_legal_move(board, res) && (bitset & (1 << res)));
    return res;
    for (uint8_t i = 0; i < 7; i++)
        if (bitset & (1 << i))
            return i;
    // If that happens I'll die on the spot
    abort();
}

extern "C" {
/**
 * Makes a move on the board
 * The AI has total access to the board which means it
 * can cheat pretty easily (Pls don't)
*/
void play_move(board_t *board, void **data)
{
    std::cout << "AI plays a random move" << std::endl;
    while (1) {
        int i = get_winning_move(board);
        if (i == -1)
            i = get_non_losing_move(board);
        if (is_legal_move(board, i)) {
            place_piece(board, i, PLAYER_O);
            return;
        }
    }
    // No legal move, should never happen
    abort();
}
}

extern "C" {
/**
 * Destroys the personal datastore of the AI
 * The implementation of this function is completely
 * optional ! Especially if the init has not been implemented
*/
void destroy(void **data)
{

}
}