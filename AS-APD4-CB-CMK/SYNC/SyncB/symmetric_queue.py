import threading

n_followers = 4
n_leaders = 4

tf_status = [False for _ in range(n_followers)]
followerQueue = threading.Semaphore(0)

tl_status = [False for _ in range(n_leaders)]
leadersQueue = threading.Semaphore(0)

rendezvous = threading.Semaphore(0)

def work_followers(number: int):
    tf_status[number] = True
    if followers > 0:
        followers -= 1
        followerQueue.signal()
    else:
        leaders += 1
        leadersQueue.wait()
    rendezvous.wait()

def work_leaders(number: int):
    tl_status[number] = True
    if leaders > 0:
        leaders -= 1
        leadersQueue.signal()
    else:
        followers += 1
        followerQueue.wait()
    rendezvous.signal()

threads = [
        threading.Thread(target=work_followers, args=(0, ))
    ]

for i in threads:
    i.start()
for i in threads:
    i.join()