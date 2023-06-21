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

        hydrogenSemaphore.wait()
        oxygenSemaphore.signal()

        hydrogenPipet.signal()


def Oxygen():
    while True:
        oxygenPipet.wait()

        hydrogenSemaphore.signal()
        hydrogenSemaphore.signal()

        oxygenSemaphore.wait()

        oxygenPipet.signal()


def setup():
    for i in range(maxHydrogen.v):
      subscribe_thread(Hydrogen)
    for i in range(maxOxygen.v):
      subscribe_thread(Oxygen)