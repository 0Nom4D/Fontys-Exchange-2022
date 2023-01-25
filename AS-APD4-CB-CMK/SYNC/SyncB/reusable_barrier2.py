import threading

n = 4 # Number of threads

mutex = threading.Lock()
tt = [False for _ in range(n)]
tt2 = [False for _ in range(n)]

def work(number: int):
    print("ayo")
    tt[number] = True
    while not all(tt):
        pass

    # critical point
    print("critical point")

    tt2[number] = True
    while not all(tt2):
        pass
    print("ayo2")

threads = [threading.Thread(target=work, args=(i, )) for i in range(n)]
for i in threads:
    i.start()
for i in threads:
    i.join()