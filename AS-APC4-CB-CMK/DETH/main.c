#include <stdbool.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <dlfcn.h>

#include "common.h"

/**
 * data is the data store used (or not) by the AI,
 * it is really useful in case you want to have caching
*/
typedef struct {
    void *data;
    void (*init)(void **);
    void (*play_move)(board_t *, void **);
    void (*destroy)(void **);
} ai_store_t;

static const char *prompt = "$> ";

void init_board(board_t *board)
{
    for (int i = 0; i < BOARD_SIZE; ++i)
        board->data[i] = NO_PLAYER;
}

void print_prompt(void)
{
    write(1, prompt, strlen(prompt));
}

bool handle_input(board_t *board, const char *input)
{
    if (input[0] > '7' || input[0] < '1')
        return false;
    uint8_t chosen_column = input[0] - '1';

    if (!is_legal_move(board, chosen_column))
        return false;
    place_piece(board, chosen_column, PLAYER_X);
    return true;
}

bool play_player(board_t *board)
{
    // Literally stolen from my shell xd
    char *input = NULL;
    size_t read_size_line = 0;
    size_t is_read = 0;

    do {
        display_game(board);
        print_prompt();
        is_read = getline(&input, &read_size_line, stdin);
        if (is_read != (size_t) (-1) && input[0] != '\n')
            if (handle_input(board, input))
                return true;
    } while (input && is_read != (size_t) (-1));
    return false;
}

/**
 * Makes the AI play its move
*/
void play_ai(board_t *board, ai_store_t *ai_store)
{
    ai_store->play_move(board, ai_store->data);
}

void loop(board_t *board, ai_store_t *ai_store)
{
    while (1) {
        if (!play_player(board))
            return;
        if (check_win(board, PLAYER_X, "Human", true))
            return;
        ai_store->play_move(board, ai_store->data);
        if (check_win(board, PLAYER_O, "AI", true))
            return;
    }    
}

int main(int argc, const char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "Not enough arguments\n");
        return 1;
    }
    // Load .so
    void *ai_handle = dlopen(argv[1], RTLD_LAZY);
    if (!ai_handle) {
        fprintf(stderr, "%s\n", dlerror());
        return 1;
    }

    // Load the functions
    ai_store_t ai_store = {
        .data = NULL,
        .destroy = NULL,
        .init = NULL,
        .play_move = NULL,
    };
    ai_store.destroy = dlsym(ai_handle, "destroy");
    if (!ai_store.destroy) {
        fprintf(stderr, "%s\n", dlerror());
        return 1;
    }
    ai_store.init = dlsym(ai_handle, "init");
    if (!ai_store.init) {
        fprintf(stderr, "%s\n", dlerror());
        return 1;
    }
    ai_store.play_move = dlsym(ai_handle, "play_move");
    if (!ai_store.play_move) {
        fprintf(stderr, "%s\n", dlerror());
        return 1;
    }

    // Init AI
    ai_store.init(&ai_store.data);

    // Play game
    board_t board;
    init_board(&board);
    loop(&board, &ai_store);
    return 0;
}