from Environment import *

maxPhilosophers = 5
mutex = MyMutex("Dining Philosopher Mutex")

idxList = [idx for idx in range(maxPhilosophers)]

philosophers = [
    MyConditionVariable(mutex, f"Philosopher {idx}")
    for idx in range(maxPhilosophers)
]
forkStates = [
    MyBool(True, f"Fork {idx} state")
    for idx in range(maxPhilosophers)
]

def diningLoop():

    def left(i):
        return i

    def right(i):
        return (i + 1) % maxPhilosophers

    def getForks(forkId_1: int, forkId_2: int):
        forkStates[forkId_1].v = forkStates[forkId_2].v = False

    def freeForks(forkId_1: int, forkId_2: int):
        forkStates[forkId_1].v = forkStates[forkId_2].v = True

    i = idxList.pop()
    while True:
        mutex.wait()

        ## Checking if left and right fork
        while not(forkStates[left(i)].v and forkStates[right(i)].v):
            philosophers[i].wait()

        ## Making philosopher at index i take the forks
        getForks(left(i), right(i))
        mutex.signal()

        mutex.wait()
        ## Making philosopher at index i release the forks
        freeForks(left(i), right(i))
        philosophers[left(i)].notify()
        philosophers[right(i)].notify()
        mutex.signal()

def setup():
    for _ in range(maxPhilosophers):
      subscribe_thread(diningLoop)
