from Environment import *

n = 4 # Number of threads

m = MyMutex("Mutex 1")
tt = [MySemaphore(0, f"Semaphore 1 - {_}") for _ in range(n)]
tt2 = [MySemaphore(0, f"Semaphore 2 - {_}") for _ in range(n)]

def work(number: int):
    while True:
        tt[number].signal()
        print(number)
        for i in range(n):
            tt[i].wait()
        for i in range(n):
            tt[i].signal()

        # critical point
        m.wait()
        print("critical point")
        m.signal()

        tt2[number].signal()
        for i in range(n):
            tt2[i].wait()
        for i in range(n):
            tt2[i].signal()

def setup():
    subscribe_thread(lambda: work(0))
    subscribe_thread(lambda: work(1))
    subscribe_thread(lambda: work(2))
    subscribe_thread(lambda: work(3))
