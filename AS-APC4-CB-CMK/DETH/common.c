#include "common.h"

#ifdef __cplusplus
extern "C" {
#endif

#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>

void display_game(const board_t *board)
{
    char output[] =
            "|AAAAAAA|\n"
            "|AAAAAAA|\n"
            "|AAAAAAA|\n"
            "|AAAAAAA|\n"
            "|AAAAAAA|\n"
            "|AAAAAAA|\n"
            " 1234567 \n";

    for (int y = 0; y < 6; ++y) {
        for (int x = 0; x < 7; ++x) {
            switch (board->data[x + y * BOARD_WIDTH]) {
                case PLAYER_O:
                    output[((BOARD_WIDTH + 3) * y + 1 + x)] = 'O';
                    break;
                case PLAYER_X:
                    output[((BOARD_WIDTH + 3) * y + 1 + x)] = 'X';
                    break;
                case NO_PLAYER:
                    output[((BOARD_WIDTH + 3) * y + 1 + x)] = ' ';
                    break;
            }
        }
    }
    write(1, output, 70);
}

static inline void announce_win(const board_t *board, const char *name_player)
{
    display_game(board);
    printf("%s wins !\n", name_player);
}

bool is_board_full(const board_t *board)
{
    for (int j = 0; j < 7; j++) {
        for (int i = 5; i >= 0; i--) {
            if (board->data[AT_BOARD(j, i)] == NO_PLAYER)
                return false;
        }
    }
    return true;
}

bool check_win(const board_t *board, board_status_t player, const char *name_player, bool announce)
{
    // AUGH
    for (int x = 0; x < 4; x++) {
        for (int y = 0; y < 6; y++) {
            if (board->data[AT_BOARD(x, y)] == player &&
                board->data[AT_BOARD(x + 1, y)] == player &&
                board->data[AT_BOARD(x + 2, y)] == player &&
                board->data[AT_BOARD(x + 3, y)] == player) {
                if (announce)
                    announce_win(board, name_player);
                return true;
            }
        }
    }
    for (int x = 0; x < 7; x++) {
        for (int y = 0; y < 3; y++) {
            if (board->data[AT_BOARD(x, y)] == player &&
                board->data[AT_BOARD(x, y + 1)] == player &&
                board->data[AT_BOARD(x, y + 2)] == player &&
                board->data[AT_BOARD(x, y + 3)] == player) {
                if (announce)
                    announce_win(board, name_player);
                return true;
            }
        }
    }
    for (int x = 0; x < 4; x++) {
        for (int y = 0; y < 3; y++) {
            if (board->data[AT_BOARD(x, y)] == player &&
                board->data[AT_BOARD(x + 1, y + 1)] == player &&
                board->data[AT_BOARD(x + 2, y + 2)] == player &&
                board->data[AT_BOARD(x + 3, y + 3)] == player) {
                if (announce)
                    announce_win(board, name_player);
                return true;
            }
        }
    }
    for (int x = 3; x < 7; x++) {
        for (int y = 0; y < 3; y++) {
            if (board->data[AT_BOARD(x, y)] == player &&
                board->data[AT_BOARD(x - 1, y + 1)] == player &&
                board->data[AT_BOARD(x - 2, y + 2)] == player &&
                board->data[AT_BOARD(x - 3, y + 3)] == player) {
                if (announce)
                    announce_win(board, name_player);
                return true;
            }
        }
    }
    return false;
}

void place_piece(board_t *board, uint8_t column, board_status_t player)
{
    for (int i = 5; i >= 0; i--) {
        if (board->data[AT_BOARD(column, i)] != NO_PLAYER)
            continue;
        board->data[AT_BOARD(column, i)] = player;
        return;
    }
    // Either something is clearly broken with the interface
    // or the AI f***ed up really bad for this to be called
    abort();
}

void remove_piece(board_t *board, uint8_t column, board_status_t player)
{
    for (int i = 0; i < 6; i++) {
        board_status_t current = board->data[AT_BOARD(column, i)];
        if (current == NO_PLAYER)
            continue;
        else if (current != player)
            abort();
        board->data[AT_BOARD(column, i)] = NO_PLAYER;
        return;
    }
    abort();
}

bool is_legal_move(const board_t *board, uint8_t column)
{
    return board->data[column] == NO_PLAYER;
}

#ifdef __cplusplus
}
#endif