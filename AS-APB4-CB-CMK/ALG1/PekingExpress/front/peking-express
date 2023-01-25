#!/usr/bin/env python3

from sources.file_handler import is_valid_file
from sources.Graph import GraphDrawer
from sources.exitCode import exitCode

from sys import argv


def get_help() -> int:
    print("USAGE")
    print("\t./peking-express [file]")
    print("\nDESCRIPTION")
    print("\tfile\tfile containing options for the game")
    return 0


def main() -> int:
    if len(argv) != 2:
        return exitCode.ERROR
    if len(argv) == 2 and (argv[1] == '-h' or argv[1] == '--help'):
        return get_help()
    content = is_valid_file(argv[1])
    if len(argv) == 2 and not content:
        return exitCode.ERROR
    drawer = GraphDrawer(content)
    return drawer.launchGame(True)


if __name__ == '__main__':
    exit(main())
