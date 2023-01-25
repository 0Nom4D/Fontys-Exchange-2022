from Environment import *

nbReindeer=MyInt(9,"Total Reindeers")
nbElf=MyInt(10,"Total Elves")

elves=MyInt(0,"Elves waiting")
reindeer=MyInt(0,"Reindeers waiting")
santaSem = MySemaphore(0,"Santa")
reindeerSem = MySemaphore(0,"Reindeer")
elfTex = MySemaphore(1,"Elf block entering")
elfWait = MySemaphore(0,"Elf waiting for santa")
mutex = MyMutex("mutex")

def Santa():
    while True:
        santaSem.wait()
        mutex.wait()

        if elves.v >= 3:
            print("\nhelping elves")
            elfWait.signal(elves.v)
        elif reindeer.v >= 9:
            print("\npreparing sleigh")
            reindeerSem.signal(9)
            reindeer.v -= 9
        mutex.signal()

def Reindeer():
    while True:
        mutex.wait()
        reindeer.v += 1
        if reindeer.v == 9:
            santaSem.signal()
        mutex.signal()

        reindeerSem.wait()
        print("reindeer hitched")

def Elf():
    while True:
        elfTex.wait()
        mutex.wait()
        elves.v += 1
        if elves.v >= 3:
            santaSem.signal()
        elfTex.signal()
        mutex.signal()

        elfWait.wait()
        print("elf getting help")

        mutex.wait()
        elves.v -= 1
        if elves.v == 0:
            elfTex.signal()
        mutex.signal()

def setup():
    subscribe_thread(Santa)
    for i in range(nbReindeer.v):
      subscribe_thread(Reindeer)
    for i in range(nbElf.v):
      subscribe_thread(Elf)