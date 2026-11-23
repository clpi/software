"""Count POSIX writes on a fresh regular file and check every output byte."""
import os
import struct
import tempfile


def capture(records, group):
    calls = 0
    with tempfile.TemporaryFile() as output:
        for offset in range(0, len(records), group):
            payload = b"".join(records[offset : offset + group])
            written = os.write(output.fileno(), payload)
            calls += 1
            if written != len(payload):
                raise RuntimeError("short write: this venue failed the full-write assumption")
        output.seek(0)
        return calls, output.read()


def verify(count):
    records = [struct.pack(">I", number) for number in range(count)]
    expected = b"".join(records)
    before, old = capture(records, 1)
    after, new = capture(records, 64)
    if old != expected or new != expected:
        raise ValueError("ordered bytes changed")
    if before != count or after != (count + 63) // 64:
        raise ValueError("write count exceeded the tight capacity bound")
    return before, after, len(expected)


if __name__ == "__main__":
    for n in (0, 1, 63, 64, 65, 127, 128, 129, 4096):
        before, after, size = verify(n)
        print(f"{n} records | {before} -> {after} writes | {size} identical bytes")
