from Environment import *
from Environment import _blk
from dataclasses import dataclass

N = 4

@dataclass
class Person:
    count: MyInt
    cv: MyConditionVariable
    state_walk: str
    state_trans: str

state = MyString("NEUTRAL", "state")
mutex = MyMutex("mutex")
heathen = Person(MyInt(0, "heathenCount"),
  MyConditionVariable(mutex, "heathenCV"),"HEATHENS_RULE","TRANS_TO_PRUDES")
prude = Person(MyInt(0, "prudeCount"),
  MyConditionVariable(mutex, "prudeCV"), "PRUDES_RULE", "TRANS_TO_HEATHENS")

def threadPerson(me: Person, other: Person):
    while True:
        mutex.wait()
        if state.v == other.state_walk:
            state.v = other.state_trans
        while not (state.v == "NEUTRAL" or state.v == me.state_walk):
            me.cv.wait()
        state.v = me.state_walk

        me.count.v += 1
        mutex.signal()

        # CS

        mutex.wait()
        me.count.v -= 1
        if me.count.v == 0:
            state.v = "NEUTRAL"
            other.cv.notify_all()
        mutex.signal()

def setup():
    for i in range(N):
        subscribe_thread(lambda: threadPerson(heathen, prude))
    for i in range(N):
        subscribe_thread(lambda: threadPerson(prude, heathen))
