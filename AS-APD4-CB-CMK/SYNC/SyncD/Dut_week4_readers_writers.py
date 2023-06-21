from Environment import *

ressourceMutex = MyMutex("Mutex")

isWriterWriting = MyBool(False, "Writer's Writing State")
wBusyCount = MyInt(0, "Number of writers waiting")
rBusyCount = MyInt(0, "Number of readers waiting")

ressourceCV = MyConditionVariable(
    ressourceMutex, "Conditional Variable for Shared Ressource"
)

def doReading():
    print(f"Reader is reading.")

def doWriting():
    print(f"Writer is writing.")

def readersLoop():
    while True:
        ressourceMutex.wait()

        ## Checking writer's priority (if writer is about to write / is writing, waits)
        while wBusyCount.v > 0 or isWriterWriting.v:
            ressourceCV.wait()
        rBusyCount.v += 1
        ressourceMutex.signal()

        doReading()

        ressourceMutex.wait()
        rBusyCount.v -= 1

        ## Notifies all threads to check if condition has changed
        if not rBusyCount.v:
            ressourceCV.notify_all()
        ressourceMutex.signal()

def writersLoop():
    while True:
        ressourceMutex.wait()

        ## Telling program that a writer is waiting
        isWriterWriting.v = True
        while rBusyCount.v > 0 or wBusyCount.v > 0:
            ressourceCV.wait()

        ## Telling program that a writer doesn't wait anymore
        isWriterWriting.v = False
        wBusyCount.v += 1
        doWriting()
        ressourceMutex.signal()

        ressourceMutex.wait()
        wBusyCount.v -= 1

        ## Notifies all threads to check if condition has changed
        ressourceCV.notify_all()
        ressourceMutex.signal()

def setup():
    for _ in range(7):
        subscribe_thread(readersLoop)
    for _ in range(7):
        subscribe_thread(writersLoop)
