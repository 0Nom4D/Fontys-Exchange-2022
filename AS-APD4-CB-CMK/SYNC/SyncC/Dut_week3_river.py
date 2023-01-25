from Environment import *

maxSerf = MyInt(5, "Max number of Serf Threads")
maxHacker = MyInt(5, "Max number of Hacker Threads")
serfCounter = MyInt(0, "Serf Counter")
hackerCounter = MyInt(0, "Hacker Counter")
hQueue = MySemaphore(0, "Hacker queue")
sQueue = MySemaphore(0, "Serf queue")
boatBarrier = MySemaphore(4, "Boat Barrier")
mutex = MySemaphore(1, "Filling Boat Mutex")
isCaptain = MyBool(False, "Bool for Captain Status")

def hackerLoop():
    while True:
        mutex.wait()
        isCaptain.v = False
        hackerCounter.v += 1
        if hackerCounter.v == 4:
            hQueue.signal(4)
            hackerCounter.v = 0
            isCaptain.v = True
        elif hackerCounter.v == 2 and serfCounter.v >= 2:
            hQueue.release(2)
            sQueue.release(2)
            hackerCounter.v = 0
            serfCounter.v -= 2
            isCaptain.v = True
        else:
            mutex.signal()
        hQueue.wait()
        print("Boarding the boat")
        boatBarrier.wait()
        if isCaptain.v:
            print("Rowing the boat!")
            boatBarrier.signal(4)
            mutex.signal()

def serfLoop():
    while True:
        mutex.wait()
        isCaptain.v = False
        serfCounter.v += 1
        if serfCounter.v == 4:
            sQueue.signal(4)
            serfCounter.v = 0
            isCaptain.v = True
        elif hackerCounter.v >= 2 and serfCounter.v == 2:
            hQueue.release(2)
            sQueue.release(2)
            hackerCounter.v -= 2
            serfCounter.v = 0
            isCaptain.v = True
        else:
            mutex.signal()
        sQueue.wait()
        print("Boarding the boat")
        boatBarrier.wait()
        if isCaptain.v:
            print("Rowing the boat!")
            boatBarrier.signal(4)
            mutex.signal()

def setup():
    for i in range(maxHacker.v):
      subscribe_thread(hackerLoop)
    for i in range(maxSerf.v):
      subscribe_thread(serfLoop)