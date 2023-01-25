#!/usr/bin/env python3

import threading

sem = [
    threading.Semaphore(0),
    threading.Semaphore(0),
    threading.Semaphore(0),
    threading.Semaphore(0),
    threading.Semaphore(0),
    threading.Semaphore(0),
    threading.Semaphore(0),
]


def threadA():
    print(1)
    sem[0].release()
    sem[3].acquire()
    print(5)
    sem[4].release()

def threadB():
    sem[0].acquire()
    print(2)
    sem[1].release()
    sem[4].acquire()
    print(6)
    sem[5].release()

def threadC():
    sem[1].acquire()
    print(3)
    sem[2].release()
    sem[5].acquire()
    print(7)
    sem[6].release()

def threadD():
    sem[2].acquire()
    print(4)
    sem[3].release()
    sem[6].acquire()
    print(8)

def main():
    threads = [
        threading.Thread(target=threadA),
        threading.Thread(target=threadB),
        threading.Thread(target=threadC),
        threading.Thread(target=threadD),
    ]
    for i in threads:
        i.start()
    for i in threads:
        i.join()


if __name__ == "__main__":
    main()
