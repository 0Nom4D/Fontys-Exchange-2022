from Environment import *

maxCanivoreCooks = 5
maxVegetarianCooks = 5
maxCanivoreSavages = 5
maxVegetarianSavages = 5

mutex = MyMutex("Mutex")

servingsList = MyBag(6, "All servings")
vegePotVariable = MyConditionVariable(
    mutex, "Conditional Variable for Vegetarian"
)
carnPotVariable = MyConditionVariable(
    mutex, "Conditional Variable for Canivore"
)

def CanivoreSavages():
    while True:
        mutex.wait()
        print("Waiting until a carnivore servings is available.")
        while not servingsList.contains("CARNIVORE"):
            carnPotVariable.wait()
        print("Removing a carnivore meal")
        servingsList.get("CARNIVORE")
        carnPotVariable.notify()
        mutex.signal()

def VegeSavages():
    while True:
        mutex.wait()
        print("Waiting until a veggie servings is available.")
        while not servingsList.contains("VEGGIE"):
            vegePotVariable.wait()
        print("Removing a veggie meal")
        servingsList.get("VEGGIE")
        vegePotVariable.notify()
        mutex.signal()

def CanivoreCook():
    while True:
        mutex.wait()
        print("Checks if there already is a carnivore meal.")
        while servingsList.contains("CARNIVORE"):
            carnPotVariable.wait()
        print("Making a carnivore meal")
        servingsList.put("CARNIVORE")
        carnPotVariable.notify()
        mutex.signal()

def VegeCook():
    while True:
        mutex.wait()
        print("Checking if there already is a veggie meal")
        while servingsList.contains("VEGGIE"):
            vegePotVariable.wait()
        print("Making a veggie meal")
        servingsList.put("VEGGIE")
        vegePotVariable.notify()
        mutex.signal()

def setup():
    subscribe_thread(VegeCook)
    subscribe_thread(CanivoreCook)
    for i in range(maxCanivoreSavages):
        subscribe_thread(CanivoreSavages)
    for i in range(maxVegetarianSavages):
        subscribe_thread(VegeSavages)
