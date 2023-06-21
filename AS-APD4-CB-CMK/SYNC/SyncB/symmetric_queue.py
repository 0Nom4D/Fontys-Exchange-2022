from Environment import *

nb_followers = 5
nb_leaders = 5

leader_pipet = MySemaphore(1, "Leader Pipet")
follower_pipet = MySemaphore(1, "Follower Pipet")

leader_semaphore = MySemaphore(0, "Leader waiting")
follower_semaphore = MySemaphore(0, "Follower waiting")

def follower_thread():
    while True:
        follower_pipet.wait()

        follower_semaphore.signal()
        leader_semaphore.wait()

        print("Follower goes dancing.")

        follower_pipet.signal()

def leader_thread():
    while True:
        leader_pipet.wait()

        follower_semaphore.wait()
        leader_semaphore.signal()

        print("Leader goes dancing.")

        leader_pipet.signal()

def setup():
    for _ in range(nb_followers):
        subscribe_thread(follower_thread)
    for _ in range(nb_leaders):
        subscribe_thread(leader_thread)