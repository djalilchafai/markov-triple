#!/usr/bin/env python3
"""Fail if a frozen file's SHA-256 differs from frozen-manifest.json.

Usage: scripts/check_frozen.py            check
       scripts/check_frozen.py --update   (re)write hashes (drafter only; keeps statuses)
"""
import hashlib, json, os, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
mpath = os.path.join(root, "frozen-manifest.json")

def sha(path):
    with open(os.path.join(root, path), "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()

manifest = json.load(open(mpath))
if "--update" in sys.argv:
    for e in manifest["files"]:
        e["sha256"] = sha(e["path"])
    json.dump(manifest, open(mpath, "w"), indent=2); open(mpath, "a").write("\n")
    print("manifest updated"); sys.exit(0)

bad = 0
listed = set()
for e in manifest["files"]:
    listed.add(e["path"])
    if not os.path.exists(os.path.join(root, e["path"])):
        print("MISSING", e["path"]); bad += 1
    elif sha(e["path"]) != e["sha256"]:
        print("CHANGED", e["path"], "(status %s)" % e["status"]); bad += 1
fdir = os.path.join(root, "MarkovTriple", "Frozen")
for dp, dn, fn in sorted(os.walk(fdir)):   # E2: scan all subdirectories
    for n in sorted(fn):
        p = os.path.relpath(os.path.join(dp, n), root).replace(os.sep, "/")
        if n.endswith(".lean") and p not in listed:
            print("UNLISTED", p); bad += 1
print("OK" if not bad else "FAILED"); sys.exit(1 if bad else 0)
