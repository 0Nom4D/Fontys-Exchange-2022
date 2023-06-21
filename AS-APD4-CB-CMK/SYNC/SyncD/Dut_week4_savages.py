from Environment import *

bagMutex = MyMutex("Bag Mutex")
servingsList = MyBag(6, "All servings")

vegeSavageMutex = MyMutex("Vege Savage")
vegePotVariable = MyConditionVariable(vegeSavageMutex, "Vege Cond")
vegeCookTrigger = MySemaphore(0, "Vege Cook Trigger")

carnSavageMutex = MyMutex("Carn Savage")
carnPotVariable = MyConditionVariable(carnSavageMutex, "Carn Cond")
carnCookTrigger = MySemaphore(0, "Carn Cook Trigger")

def CanivoreSavages():
    while True:
        carnSavageMutex.wait()

        ## Triggers the vegetarian cook to make a carnivore serving
        carnCookTrigger.signal()

        ## Checks and wait for the bag to contain a carnivore serving
        bagMutex.wait()
        while not servingsList.contains("CARNIVORE"):
            bagMutex.signal()
            carnPotVariable.wait()
            bagMutex.wait()

        ## Removing the carnivore serving, still being inside the mutex lock
        servingsList.get("CARNIVORE")
        bagMutex.signal()
        carnSavageMutex.signal()

def VegeSavages():
    while True:
        vegeSavageMutex.wait()

        ## Triggers the vegetarian cook to make a veggie serving
        vegeCookTrigger.signal()

        ## Checks and wait for the bag to contain a veggie serving
        bagMutex.wait()
        while not servingsList.contains("VEGGIE"):
            bagMutex.signal()
            vegePotVariable.wait()
            bagMutex.wait()

        ## Removing the veggie serving, still being inside the mutex lock
        servingsList.get("VEGGIE")
        bagMutex.signal()
        vegeSavageMutex.signal()

def CanivoreCook():
    while True:
        ## Waiting to be triggered
        carnCookTrigger.wait()

        ## Cooking a carnivore serving
        bagMutex.wait()
        servingsList.put("CARNIVORE")
        bagMutex.signal()

        ## Notifying Savages for a new carnivore serving
        carnPotVariable.notify_all()

def VegeCook():
    while True:
        ## Waiting to be triggered
        vegeCookTrigger.wait()

        ## Cooking a veggie serving
        bagMutex.wait()
        servingsList.put("VEGGIE")
        bagMutex.signal()

        ## Notifying Savages for a new veggie serving
        vegePotVariable.notify_all()

def setup():
    subscribe_thread(VegeCook)
    subscribe_thread(CanivoreCook)
    for _ in range(5):
        subscribe_thread(CanivoreSavages)
    for _ in range(5):
        subscribe_thread(VegeSavages)
