from itertools import product

def rSubset(r):
    yield from product(*([r] * 6))

def char_to_num(c) -> int:
    if c == '.':
        return 0
    elif c == '1':
        return 1
    elif c == '2':
        return 2
    elif c == 'X':
        return 3
    assert(False)

def subset_to_pattern(ss: str) -> int:
    value = 0
    value |= char_to_num(ss[0]) << 10
    value |= char_to_num(ss[1]) << 8
    value |= char_to_num(ss[2]) << 6
    value |= char_to_num(ss[3]) << 4
    value |= char_to_num(ss[4]) << 2
    value |= char_to_num(ss[5])
    return value

# Driver Function
if __name__ == "__main__":
    i = 0
    for subset in rSubset('12.X'):
        tmp = str(''.join(subset))
        print(f"case {subset_to_pattern(tmp)}: return {i};")
        i += 1
