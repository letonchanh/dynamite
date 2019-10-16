import random

def loop(x, y):
    print('vtrace0: {}, {}'.format(x, y))
    cnt = 0
    bnd = random.randint(1, 1000)
    while x >= 0:
        if (cnt > bnd):
            break
        else:
            cnt = cnt + 1
        print('vtrace1: {}, {}'.format(x, y))
        x = x + y
    if (cnt <= bnd):
        print('vtrace2: {}, {}'.format(x, y))

def main():
    x = random.randint(0, 100);
    y = random.randint(-10, 10);
    loop(x, y)

if __name__ == "__main__":
    main()
