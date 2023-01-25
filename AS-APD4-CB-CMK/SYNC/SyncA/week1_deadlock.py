#!/usr/bin/env python3

import threading
import logging
import time
import random

semA = threading.Semaphore(1)
semB = threading.Semaphore(0)
semC = threading.Semaphore(0)

def threadA():
    while True:
        semA.acquire()
        time.sleep(0.5)
        logging.info("Thread A did some work")
        if random.randint(0, 1000000) != 42:
            semB.release()

def threadB():
    while True:
        semB.acquire()
        time.sleep(0.5)
        logging.info("Thread B did some work")
        semC.release()

def threadC():
    while True:
        semC.acquire()
        time.sleep(0.5)
        logging.info("Thread C did some work")
        semA.release()

def main():
    threads = [
        threading.Thread(target=threadA),
        threading.Thread(target=threadB),
        threading.Thread(target=threadC),
    ]
    for i in threads:
        i.start()
    for i in threads:
        i.join()

if __name__ == "__main__":
    format = "%(asctime)s: %(message)s"
    logging.basicConfig(format=format, level=logging.INFO,
                        datefmt="%H:%M:%S")
    main()
