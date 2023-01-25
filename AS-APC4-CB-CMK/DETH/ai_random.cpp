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
        auto i = dist(rng);
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