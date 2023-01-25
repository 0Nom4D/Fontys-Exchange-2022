from itertools import product

def rSubset(r):
    yield from product(*([r] * 6))

# Driver Function
if __name__ == "__main__":
    for subset in rSubset('12.X'):
        print(str(''.join(subset)))
