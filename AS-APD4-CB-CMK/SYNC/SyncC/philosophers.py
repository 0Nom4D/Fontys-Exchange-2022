from threading import Lock, Semaphore, Thread

n = 5

footman = Lock()

philosophers = [
    Semaphore(1),
    Semaphore(1),
    Semaphore(1),
    Semaphore(1),
    Semaphore(1),
]

def diningLoop(idx: int):

    def left(i):
        return i

    def right(i):
        return (i + 1) % n

    def getForks(i):
        footman.acquire()
        philosophers[right(i)].acquire()
        philosophers[left(i)].acquire()

    def putForks(i):
        philosophers[right(i)].release()
        philosophers[left(i)].release()
        footman.release()

    while True:
        print(f"Philosopher n°{idx} is thinking.")
        getForks(idx)
        print(f"Philosopher n°{idx} is dining.")
        putForks(idx)


if __name__ == "__main__":
    threads = [Thread(target=diningLoop, args=(i, )) for i in range(n)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
