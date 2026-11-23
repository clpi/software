"""Check an explicitly wrapping 16-bit lane against wide integer summation."""
import ctypes
import random


def collect(samples, cap):
    wide = flushes = 0
    for start in range(0, len(samples), cap):
        lane = ctypes.c_uint16(0)
        for x in samples[start:start+cap]:
            lane.value += x
        wide += lane.value
        flushes += 1
    return wide, flushes


def verify():
    rng = random.Random(4096)
    runs = 0
    for size in (0, 1, 256, 257, 258, 4095, 4096, 4097):
        for xs in ([255]*size, [0]*size, [rng.randrange(256) for _ in range(size)]):
            for cap in (64, 257):
                result, calls = collect(xs, cap)
                if (result, calls) != (sum(xs), (size+cap-1)//cap):
                    raise ValueError("sum or flush count changed")
                runs += 1
    if collect([255]*258,258)[0] != 254:
        raise ValueError("wrap counterexample failed")
    print(f"{runs} bounded lane checks; 4096 bytes: 64 -> 16 flushes; unsafe 258-byte lane wraps to 254")


if __name__ == "__main__":
    verify()
