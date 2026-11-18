"""Update one leaf; compare every cached digest with an independent clean tree."""
import hashlib


class CountedHash:
    def __init__(self):
        self.calls = 0

    def __call__(self, data):
        self.calls += 1
        return hashlib.sha256(data).digest()


def build(values, digest):
    leaves = [digest(b"\x00" + value) for value in values]
    levels = [leaves]
    while len(levels[-1]) > 1:
        previous = levels[-1]
        current = []
        for offset in range(0, len(previous), 2):
            current.append(digest(b"\x01" + previous[offset] + previous[offset + 1]))
        levels.append(current)
    return levels


def repair(levels, index, replacement, digest):
    value = digest(b"\x00" + replacement)
    trace = []
    for level, row in enumerate(levels):
        trace.append((level, index))
        row[index] = value
        if len(row) > 1:
            left = index - index % 2
            value = digest(b"\x01" + row[left] + row[left + 1])
            index //= 2
    return trace


def verify():
    values = [i.to_bytes(4, "big") for i in range(1024)]
    original = build(values, CountedHash())
    for index in range(len(values)):
        edited = values.copy()
        edited[index] = b"edited/" + values[index]
        full, incremental = CountedHash(), CountedHash()
        expected = build(edited, full)
        old = [row.copy() for row in original]
        trace = repair(old, index, edited[index], incremental)
        if old != expected or expected[-1] == original[-1]:
            raise ValueError(f"bad cached digest after edit {index}")
        if trace != [(level, index >> level) for level in range(11)]:
            raise ValueError("incorrect ancestor path")
        if (full.calls, incremental.calls) != (2047, 11):
            raise ValueError("incorrect number of hashes")
    print("1024 single-leaf edits | 2047 -> 11 SHA-256 calls per edit | every cached digest matched")


if __name__ == "__main__":
    verify()
