import threading

n = 4 # Number of threads

tt = [threading.Semaphore(0) for _ in range(n)]
tt2 = [threading.Semaphore(0) for _ in range(n)]

def work(number: int):
    print("ayo")
    tt[number].release()
    for i in range(n):
        tt[i].acquire()
    for i in range(n):
        tt[i].release()

    # critical point
    print("critical point")

    tt2[number].release()
    for i in range(n):
        tt2[i].acquire()
    for i in range(n):
        tt2[i].release()
    print("ayo2")

threads = [threading.Thread(target=work, args=(i, )) for i in range(n)]
for i in threads:
    i.start()
for i in threads:
    i.join()