from os.path import exists
from typing import Union, Any
from json import load


def is_valid_file(filename: str) -> Union[bool, Any]:
    if not exists(filename):
        return False
    with open(filename) as fd:
        options = load(fd)
    return options
