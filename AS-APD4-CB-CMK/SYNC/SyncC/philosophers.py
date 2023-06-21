from Environment import *

n = 5

footman = MySemaphore(4, "mutex")

philosophers = [
    MySemaphore(1, "Semaphore 1"),
    MySemaphore(1, "Semaphore 2"),
    MySemaphore(1, "Semaphore 3"),
    MySemaphore(1, "Semaphore 4"),
    MySemaphore(1, "Semaphore 5"),
]

def diningLoop(idx: int):

    def left(i):
        return i

    def right(i):
        return (i + 1) % n

    def getForks(i):
        footman.wait()
        philosophers[right(i)].wait()
        philosophers[left(i)].wait()

    def putForks(i):
        philosophers[right(i)].signal()
        philosophers[left(i)].signal()
        footman.signal()

    while True:
        print(f"Philosopher n°{idx} is thinking.")
        getForks(idx)
        print(f"Philosopher n°{idx} is dining.")
        putForks(idx)


def setup():
    subscribe_thread(lambda: diningLoop(0))
    subscribe_thread(lambda: diningLoop(1))
    subscribe_thread(lambda: diningLoop(2))
    subscribe_thread(lambda: diningLoop(3))
    subscribe_thread(lambda: diningLoop(4))
