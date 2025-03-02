
def fibonacci(n):
    if n <= 0:
        return []
    elif n == 1:
        return [0]
    elif n == 2:
        return [0, 1]

    fib_seq = [0, 1]
    for i in range(2, n):
        fib_seq.append(fib_seq[-1] + fib_seq[-2])

    return fib_seq

# Example usage:
if __name__ == "__main__":
    n = 10
    print(f"First {n} Fibonacci numbers: {fibonacci(n)}")
