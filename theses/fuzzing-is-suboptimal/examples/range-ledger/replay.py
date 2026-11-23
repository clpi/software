"""Route each sampled position to a bank; compare the actual routes."""
def route(a, b):
    return tuple(dict.fromkeys(position // 16 for position in range(a, b)))


def verify():
    raw = [(a,b) for a in range(65) for b in range(a,65)]
    representatives = [(0,0)] + [(16*i,16*j+1) for i in range(4) for j in range(i,4)]
    observed = {route(a,b) for a,b in raw}
    if {route(a,b) for a,b in representatives} != observed or len(observed) != 11:
        raise RuntimeError("lost a routed bank signature")
    print(f"{len(raw)} -> {len(representatives)} intervals; all {len(observed)} executed routes retained")


if __name__ == "__main__":
    verify()
