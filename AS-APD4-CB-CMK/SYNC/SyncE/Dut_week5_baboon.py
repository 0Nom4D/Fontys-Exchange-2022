from Environment import *
from Environment import _blk

state = MyString("EMPTY", "State")
mutex = MyMutex("Mutex")

capacity = MySemaphore(5, "Baboon Capacity")

maxNorth = 5
northSem = MySemaphore(0, "North Semaphore")

maxSouth = 5
southSem = MySemaphore(0, "South Semaphore")


def threadBaboon(fromDest: MySemaphore, toDest: MySemaphore):
    while True:
        mutex.wait()
        if state.v != "EMPTY" and state.v != toDest._name and capacity.get_value() != 5:
            mutex.signal()
            continue
        capacity.wait()
        state.v = toDest._name # Ugly but it should work
        mutex.signal()

        # Cross the canyon
        print(f"Crossing canyon {str(toDest)=}")

        capacity.signal()


def setup():
    for _ in range(maxNorth):
        subscribe_thread(lambda: threadBaboon(northSem, southSem))
    for _ in range(maxSouth):
        subscribe_thread(lambda: threadBaboon(southSem, northSem))
