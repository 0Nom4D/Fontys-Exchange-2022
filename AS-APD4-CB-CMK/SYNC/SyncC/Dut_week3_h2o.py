from Environment import *

maxHydrogen = MyInt(5, "Max Hydrogen Threads")
maxOxygen = MyInt(5, "Max Oxygen Threads")

hydrogenSemaphore = MySemaphore(0, "Hydrogen waiting")
oxygenSemaphore = MySemaphore(0, "Oxygen waiting")

hydrogenPipet = MySemaphore(2, "Hydrogen Pipet")
oxygenPipet = MySemaphore(1, "Oxygen Pipet")


def Hydrogen():
    while True:
        hydrogenPipet.wait()

        ## Signaling One hydrogen and One Oxygen
        hydrogenSemaphore.signal()
        oxygenSemaphore.signal()

        ## Waiting for 2 signal of hydrogen (Oxygen class making it)
        hydrogenSemaphore.wait()
        hydrogenSemaphore.wait()

        hydrogenPipet.signal()


def Oxygen():
    while True:
        oxygenPipet.wait()

        ## Signaling Hydrogens
        hydrogenSemaphore.signal()
        hydrogenSemaphore.signal()

        ## Waiting for 2 signal of oxygenSemaphore
        oxygenSemaphore.wait()
        oxygenSemaphore.wait()

        oxygenPipet.signal()


def setup():
    for i in range(maxHydrogen.v):
      subscribe_thread(Hydrogen)
    for i in range(maxOxygen.v):
      subscribe_thread(Oxygen)