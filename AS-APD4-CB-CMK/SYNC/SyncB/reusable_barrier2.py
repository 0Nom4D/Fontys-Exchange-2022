from Environment import *

n = 4 # Number of threads

m = MyMutex("Mutex")

tt = [False for _ in range(n)]
tt2 = [False for _ in range(n)]

def work(number: int):
    tt[number] = True
    while not all(tt):
        ...

    # critical point
    m.wait()
    print("critical point")
    m.signal()

    tt2[number] = True
    while not all(tt2):
        ...

def setup():
    subscribe_thread(lambda: work(0))
    subscribe_thread(lambda: work(1))
    subscribe_thread(lambda: work(2))
    subscribe_thread(lambda: work(3))