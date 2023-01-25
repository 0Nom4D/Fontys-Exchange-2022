#ifndef BA8430C3_F5A9_40F8_919B_413A64FC30E3
#define BA8430C3_F5A9_40F8_919B_413A64FC30E3

#ifdef __cplusplus
extern "C"
{
#endif

#include "stdbool.h"
#include "stdint.h"

#define BOARD_WIDTH 7

#define BOARD_HEIGHT 6

#define BOARD_SIZE (BOARD_WIDTH * BOARD_HEIGHT)

#define AT_BOARD(column, row) ((column) + (row)*BOARD_WIDTH)

    typedef enum
    {
        PLAYER_X,
        PLAYER_O,
        NO_PLAYER,
        WALLED,
    } board_status_t;

    typedef struct
    {
        board_status_t data[BOARD_SIZE];
    } board_t;

    void display_game(const board_t *board);

    /**
     * Checks if a win has been found and prints it to stdin
     *
     * Returns true if a win has been found
     */
    bool check_win(const board_t *board, board_status_t player, const char *name_player, bool announce);

    void place_piece(board_t *board, uint8_t column, board_status_t player);

    void remove_piece(board_t *board, uint8_t column, board_status_t player);

    bool is_legal_move(const board_t *board, uint8_t column);

    bool is_board_full(const board_t *board);

#ifdef __cplusplus
}
#endif

#endif /* BA8430C3_F5A9_40F8_919B_413A64FC30E3 */
