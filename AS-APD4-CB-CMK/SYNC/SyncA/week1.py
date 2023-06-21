from Environment import *
from Environment import _blk

flags = [MyBool(False, "Flag 0"), MyBool(False, "Flag 1")]
x = [MyBool(False, "X 0"), MyBool(False, "X 1")]

def threadA():
    while True:
        _blk()
        flags[0].v = True
        _blk()
        x[1].v = False
        _blk()
        if flags[1].v:
            _blk()
            x[1].v = True
            _blk()
            flags[0].v = False
        _blk()
        while flags[1].v or x[1].v:
            _blk()
            flags[0].v = False
            _blk()
            flags[0].v = True
        _blk()
        print("Critical Section")
        _blk()
        flags[0].v = False
        _blk()
        x[0].v = False
        _blk()

def threadB():
    while True:
        _blk()
        flags[1].v = True
        _blk()
        x[0].v = False
        _blk()
        if flags[0].v:
            _blk()
            x[0].v = True
            _blk()
            flags[1].v = False
        _blk()
        while flags[0].v or x[0].v:
            _blk()
            flags[1].v = False
            _blk()
            flags[1].v = True
        _blk()
        print("Critical Section")
        _blk()
        flags[1].v = False
        _blk()
        x[1].v = False
        _blk()

def setup():
    subscribe_thread(threadA)
    subscribe_thread(threadB)