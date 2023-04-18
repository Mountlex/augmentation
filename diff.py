
done_cases = []
with open("output.txt") as file:
    done_cases = [line.rstrip() for line in file]

with open("c4_cases.txt") as file:
    while line := file.readline():
        case = line.rstrip()
        if case not in done_cases:
            print(case)