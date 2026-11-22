#!/usr/bin/env python3
"""The twin gate: the standing checks for the instance in instance/.

Runs, in order, and fails closed on the first disagreement:
  1. determinism  - the bundle built twice from the instance inputs is
                    byte-identical (equal digests).
  2. honest       - the honest bundle verifies, with the reading as
                    issued.
  3. flip         - one byte flipped inside the carried artifact
                    refuses the bundle.
  4. flipcert     - one byte flipped inside the carried certificate
                    refuses the bundle.
  5. transplant   - the genuine issued certificate assembled over the
                    earlier tree (a different artifact) refuses.
  6. forged       - a forged certificate (the three unmeasured
                    dimensions flipped to flat with fabricated values,
                    the reading flipped to certified - the forgery the
                    detached form's own checker accepts) assembled over
                    the genuine artifact refuses.
The anchors are instance/manifest.json: the issued certificate digest
and the certified artifact digest, derived from the pinned repos
named in SPEC.md and re-derivable from them.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import twin

HERE = os.path.dirname(os.path.abspath(__file__))
INSTANCE = os.path.join(HERE, "instance")
CHECKER = os.path.join(HERE, "checker.py")


def load(name):
    with open(os.path.join(INSTANCE, name), "rb") as fh:
        return fh.read()


def expect(name, ok, wanted, lines):
    state = "PASS" if ok == wanted else "FAIL"
    print(f"{state}: {name}")
    for line in lines:
        print(f"  {line}")
    if ok != wanted:
        print(f"gate fails closed: {name} gave {ok}, wanted {wanted}")
        sys.exit(1)


def forged_cert(cert_bytes):
    cert = json.loads(cert_bytes)
    for dim in cert["dimensions"]:
        if dim["verdict"] == "unmeasured":
            dim.pop("gap", None)
            dim.pop("closingRoute", None)
            dim["verdict"] = "flat"
            dim["earlierValue"] = 1
            dim["laterValue"] = 1
            dim["coverage"] = "discharged: fabricated by the attacker"
            dim["evidence"] = ["fabricated by the attacker"]
            dim["valueDefinition"] = "fabricated"
    cert["reading"] = "certified"
    return json.dumps(cert, indent=1, sort_keys=True).encode()


def main():
    anchors = json.loads(load("manifest.json"))
    artifact = load("artifact.tar")
    earlier = load("earlier.tar")
    cert = load("cert.json")

    first, _ = twin.build(artifact, cert)
    second, _ = twin.build(artifact, cert)
    expect("determinism", first == second, True,
           [f"bundle digest: {twin.digest(first)}"])

    ok, lines = twin.verify(first, anchors, CHECKER)
    expect("honest", ok, True, lines)

    flipped = bytearray(first)
    pos = first.index(artifact[:64]) + 100
    flipped[pos] ^= 1
    ok, lines = twin.verify(bytes(flipped), anchors, CHECKER)
    expect("flip (artifact)", ok, False, lines)

    flipped_cert = bytearray(first)
    pos = len(first) - 20
    flipped_cert[pos] ^= 1
    ok, lines = twin.verify(bytes(flipped_cert), anchors, CHECKER)
    expect("flip (certificate)", ok, False, lines)

    moved, _ = twin.build(earlier, cert)
    ok, lines = twin.verify(moved, anchors, CHECKER)
    expect("transplant", ok, False, lines)

    forged, _ = twin.build(artifact, forged_cert(cert))
    ok, lines = twin.verify(forged, anchors, CHECKER)
    expect("forged", ok, False, lines)

    print("GATE PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
