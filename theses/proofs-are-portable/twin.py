#!/usr/bin/env python3
"""Twin form: a release artifact carrying its certificate as a derived
component of the artifact itself.

Build assembles one bundle from an artifact and a certificate.
Assembly is not issuance and is not verification: the builder is a
dumb assembler over whatever pair it is handed. Verification is the
act that binds: it recomputes both digests from the carried bytes,
recomputes the binding digest over the two, compares the certificate
digest and the artifact digest against the anchored digests recorded
at issuance (instance/manifest.json, derived from the pinned repos
named there), checks that the certificate's own subject and pins
match the manifest, and runs the issuer's standing checker over the
carried certificate. One command, one bundle digest, both halves
checked or the bundle is refused by name.

Bundle layout:
  6 bytes   magic "TWIN1\n"
  8 bytes   big-endian length of the manifest
  manifest  canonical JSON (sorted keys, compact separators)
  artifact  artifactLength bytes
  cert      certificateLength bytes
Nothing else. Trailing bytes refuse the bundle.
"""
import hashlib
import json
import subprocess
import sys
import tempfile
import os

MAGIC = b"TWIN1\n"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def binding(artifact_digest, certificate_digest):
    raw = bytes.fromhex(artifact_digest) + bytes.fromhex(certificate_digest)
    return hashlib.sha256(raw).hexdigest()


def build(artifact, cert):
    cert_fields = json.loads(cert)
    ad = digest(artifact)
    cd = digest(cert)
    manifest = {
        "form": "twin.v1",
        "subject": cert_fields["subject"],
        "earlier": cert_fields["earlier"],
        "later": cert_fields["later"],
        "reading": cert_fields["reading"],
        "artifactDigest": ad,
        "certificateDigest": cd,
        "bindingDigest": binding(ad, cd),
        "artifactLength": len(artifact),
        "certificateLength": len(cert),
    }
    head = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
    return MAGIC + len(head).to_bytes(8, "big") + head + artifact + cert, manifest


def parse(bundle):
    if not bundle.startswith(MAGIC):
        raise ValueError("bad magic")
    off = len(MAGIC)
    hlen = int.from_bytes(bundle[off:off + 8], "big")
    off += 8
    manifest = json.loads(bundle[off:off + hlen])
    off += hlen
    alen = manifest["artifactLength"]
    clen = manifest["certificateLength"]
    artifact = bundle[off:off + alen]
    off += alen
    cert = bundle[off:off + clen]
    off += clen
    if off != len(bundle):
        raise ValueError("trailing bytes after the certificate component")
    if len(artifact) != alen or len(cert) != clen:
        raise ValueError("a component is truncated")
    return manifest, artifact, cert


def verify(bundle, anchors, checker):
    """anchors: {"certificateDigest": ..., "artifactDigest": ...} as
    recorded at issuance. checker: path to the issuer's checker.
    Returns (ok, lines)."""
    lines = []
    try:
        manifest, artifact, cert = parse(bundle)
    except Exception as exc:
        return False, [f"REFUSED: unparseable bundle: {exc}"]
    ad = digest(artifact)
    cd = digest(cert)
    if ad != manifest["artifactDigest"]:
        return False, ["REFUSED: artifact digest does not match the manifest"]
    if cd != manifest["certificateDigest"]:
        return False, ["REFUSED: certificate digest does not match the manifest"]
    if binding(ad, cd) != manifest["bindingDigest"]:
        return False, ["REFUSED: binding digest does not match the component digests"]
    if cd != anchors["certificateDigest"]:
        return False, ["REFUSED: carried certificate is not the issued certificate "
                        "(digest differs from the anchored issued digest)"]
    if ad != anchors["artifactDigest"]:
        return False, ["REFUSED: carried artifact is not the certified artifact "
                        "(digest differs from the anchored artifact digest)"]
    fields = json.loads(cert)
    for key in ("subject", "earlier", "later", "reading"):
        if fields.get(key) != manifest.get(key):
            return False, [f"REFUSED: manifest {key} differs from the carried certificate"]
    with tempfile.NamedTemporaryFile(
            "wb", suffix=".json", delete=False, dir=".") as tmp:
        tmp.write(cert)
        tmp_path = tmp.name
    try:
        run = subprocess.run([sys.executable, checker, tmp_path],
                             capture_output=True, text=True)
    finally:
        os.unlink(tmp_path)
    lines.extend(run.stdout.strip().splitlines())
    if run.returncode != 0 or "CONSISTENT" not in run.stdout:
        return False, lines + ["REFUSED: the issuer's checker does not accept "
                                "the carried certificate"]
    lines.append(f"bundle digest: {digest(bundle)}")
    lines.append(f"ACCEPT: reading as issued: {manifest['reading']}")
    return True, lines


def main(argv):
    if argv[1] == "build":
        artifact = open(argv[2], "rb").read()
        cert = open(argv[3], "rb").read()
        bundle, manifest = build(artifact, cert)
        with open(argv[4], "wb") as fh:
            fh.write(bundle)
        print(f"bundle digest: {digest(bundle)}")
        print(f"binding digest: {manifest['bindingDigest']}")
        return 0
    if argv[1] == "verify":
        bundle = open(argv[2], "rb").read()
        anchors = json.load(open(argv[3]))
        ok, lines = verify(bundle, anchors, argv[4])
        for line in lines:
            print(line)
        return 0 if ok else 1
    print("usage: twin.py build ARTIFACT CERT OUT | verify BUNDLE ANCHORS CHECKER")
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
