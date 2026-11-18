"""Check every nonempty window against a prefix-difference oracle."""
from itertools import accumulate


def verify():
    data = [(i*37+i//11)%257-125 for i in range(4096)]
    prefix = list(accumulate(data, initial=0))
    checks = 0
    for a in range(len(data)):
        streamed = 0
        for i in range(a,len(data)):
            streamed += data[i]
            if streamed != prefix[i+1]-prefix[a]:
                raise RuntimeError((a,i+1))
            checks += 1
    if checks != 8_390_656:
        raise RuntimeError("wrong interval roster")
    print(f"{checks} clean range results matched; {len(data)} singleton observations form the certified basis")


if __name__ == "__main__":
    verify()
