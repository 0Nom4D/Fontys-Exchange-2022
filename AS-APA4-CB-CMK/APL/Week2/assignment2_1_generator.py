import itertools

x = []
y = []
oneperline = []
onepercolumn = []
oneperdiagonal = [[] for _ in range(26)]

for i in range(8):
    x += [f"x{str(i)}"]
    y += [f"y{str(i)}"]
    for j in range(8):
        print(f"(declare-const x{str(i)}y{str(j)} Bool)")

print("\n;;at least one queen by line clauses")
for i in range(8):
    print("\n(assert (or", end="")
    for j in range(8):
        print(f" x{str(i)}y{str(j)}", end="")
    print("))")

print("\n;;only one queen by line clauses")
for xi in x:
    oneperline += [[]]
    for yi in y:
        oneperline[-1] += [xi + yi]

# Print clauses to check for one queen per line
for line in oneperline:
    print("\n(assert (not (or", end="")
    for comb in itertools.combinations(line, 2):
        print(f" (and {comb[0]} {comb[1]})", end="")
    print(")))")

print("\n;;only one queen by column clauses")
for yi in y:
    onepercolumn += [[]]
    for xi in x:
        onepercolumn[-1] += [xi + yi]

# Print clauses to check for one queen per column
for column in onepercolumn:
    print("\n(assert (not (or", end="")
    for comb in itertools.combinations(column, 2):
        print(f" (and {comb[0]} {comb[1]})", end="")
    print(")))")

print("\n;;only one queen by diagonal clauses")
for i in range(8):
    oneperdiagonal[0] += [f"x{str(i)}y{str(i)}"]
    oneperdiagonal[13] += [f"x{str(i)}y{str(7 - i)}"]
    if i + 1 < 8:
        oneperdiagonal[1] += [f"x{str(i)}y{str(i + 1)}"]
        oneperdiagonal[2] += [f"x{str(i + 1)}y{str(i)}"]
        oneperdiagonal[14] += [f"x{str(7 - i)}y{str(i + 1)}"]
        oneperdiagonal[15] += [f"x{str(7 - i - 1)}y{str(i)}"]
    if i + 2 < 8:
        oneperdiagonal[3] += [f"x{str(i)}y{str(i + 2)}"]
        oneperdiagonal[4] += [f"x{str(i + 2)}y{str(i)}"]
        oneperdiagonal[16] += [f"x{str(7 - i)}y{str(i + 2)}"]
        oneperdiagonal[17] += [f"x{str(7 - i - 2)}y{str(i)}"]
    if i + 3 < 8:
        oneperdiagonal[5]+=[f"x{str(i)}y{str(i + 3)}"]
        oneperdiagonal[6]+=[f"x{str(i + 3)}y{str(i)}"]
        oneperdiagonal[18]+=[f"x{str(7 - i)}y{str(i + 3)}"]
        oneperdiagonal[19]+=[f"x{str(7 - i - 3)}y{str(i)}"]
    if i + 4 < 8:
        oneperdiagonal[7]+=[f"x{str(i)}y{str(i + 4)}"]
        oneperdiagonal[8]+=[f"x{str(i + 4)}y{str(i)}"]
        oneperdiagonal[20]+=[f"x{str(7 - i)}y{str(i + 4)}"]
        oneperdiagonal[21]+=[f"x{str(7 - i - 4)}y{str(i)}"]
    if i + 5 < 8:
        oneperdiagonal[9]+=[f"x{str(i)}y{str(i + 5)}"]
        oneperdiagonal[10]+=[f"x{str(i + 5)}y{str(i)}"]
        oneperdiagonal[22]+=[f"x{str(7 - i)}y{str(i + 5)}"]
        oneperdiagonal[23]+=[f"x{str(7 - i - 5)}y{str(i)}"]
    if i + 6 < 8:
        oneperdiagonal[11]+=[f"x{str(i)}y{str(i + 6)}"]
        oneperdiagonal[12]+=[f"x{str(i + 6)}y{str(i)}"]
        oneperdiagonal[24]+=[f"x{str(7 - i)}y{str(i + 6)}"]
        oneperdiagonal[25]+=[f"x{str(7 - i - 6)}y{str(i)}"]

# Print clauses to check for one queen per diagonal
for diag in oneperdiagonal:
    if diag != []:
        print("\n(assert (not (or", end="")
        for comb in itertools.combinations(diag, 2):
            print(f" (and {comb[0]} {comb[1]})",end="")
        print(")))")

print("(check-sat)")
print("(get-model)")