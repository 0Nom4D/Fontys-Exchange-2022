from Environment import *

maxWriters = 7
maxReaders = 7

mutex = MyMutex("Mutex")

writerPriority = MyBool(True, "Writer Priority")
wBusyCount = MyInt(0, "Number of writers waiting")
rBusyCount = MyInt(0, "Number of readers waiting")
criticalData = MyInt(0, "Critical Data")

writersCV = MyConditionVariable(mutex,
"Conditional Variable for Writers")
readersCV = MyConditionVariable(mutex,
"Conditional Variable for Readers")

def doReading():
    print(f"Reader reads critical data having value {criticalData.v}.")

def doWriting():
    criticalData.v += 1
    print(f"Writer modified critical data to {criticalData.v}.")

def isAnyoneBusy():
    return not rBusyCount.v and not wBusyCount.v

def notifyPriority():
    if not isAnyoneBusy():
        if writerPriority.v:
            writersCV.notify_all()
            readersCV.notify_all()
        else:
            readersCV.notify_all()
            writersCV.notify_all()

def readersLoop():
    while True:
        mutex.wait()
        while wBusyCount.v != 0:
            readersCV.wait()
        rBusyCount.v += 1
        mutex.signal()
        doReading()
        mutex.wait()
        rBusyCount.v -= 1
        notifyPriority()
        mutex.signal()

def writersLoop():
    while True:
        mutex.wait()
        while rBusyCount.v != 0:
            readersCV.wait()
        wBusyCount.v += 1
        mutex.signal()
        doWriting()
        mutex.wait()
        wBusyCount.v -= 1
        notifyPriority()
        mutex.signal()

def setup():
    for _ in range(maxWriters):
        subscribe_thread(readersLoop)
    for _ in range(maxReaders):
        subscribe_thread(writersLoop)
