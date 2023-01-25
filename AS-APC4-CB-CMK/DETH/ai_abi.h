#ifndef B30A422C_9B19_46C6_83D7_5F037D29F4F3
#define B30A422C_9B19_46C6_83D7_5F037D29F4F3

#ifdef __cplusplus
extern "C" {
#endif

#include "common.h"

void init(void **data);

void play_move(board_t *board, void **data);

void destroy(void **data);

#ifdef __cplusplus
}
#endif

#endif /* B30A422C_9B19_46C6_83D7_5F037D29F4F3 */
