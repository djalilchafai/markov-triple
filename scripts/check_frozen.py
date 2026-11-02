#!/usr/bin/env python3
"""Fail if a frozen file's SHA-256 differs from frozen-manifest.json.

Usage: scripts/check_frozen.py            check
       scripts/check_frozen.py --update   (re)write hashes (drafter only; keeps statuses)

Two lists in the manifest:
* "files":  the frozen statements (MarkovTriple/BGL/Frozen; the legacy first surface MarkovTriple/Frozen
            was removed, DECISIONS 17); any new .lean file in that directory must be listed.
* "fenced": NON-frozen files whose *definitions* the frozen statements unfold to (M1 of the BGL
            audit: e.g. `DiffusionTriple.semigroup` = `(formData T).semigroup`).  They are hashed too,
            so a silent change of the Friedrichs construction is detected.  The check also computes
            the transitive project-import closure of every BGL/Frozen file and fails (UNFENCED) if a
            file of that closure is neither frozen nor fenced.
"""
import hashlib, json, os, re, sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
mpath = os.path.join(root, "frozen-manifest.json")

def sha(path):
    with open(os.path.join(root, path), "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()

manifest = json.load(open(mpath))
manifest.setdefault("fenced", [])
if "--update" in sys.argv:
    for e in manifest["files"] + manifest["fenced"]:
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
for fdir in (os.path.join(root, "MarkovTriple", "BGL", "Frozen"),):   # E2: scan all subdirectories
    for dp, dn, fn in sorted(os.walk(fdir)):
        for n in sorted(fn):
            p = os.path.relpath(os.path.join(dp, n), root).replace(os.sep, "/")
            if n.endswith(".lean") and p not in listed:
                print("UNLISTED", p); bad += 1
# fenced files
for e in manifest["fenced"]:
    listed.add(e["path"])
    if not os.path.exists(os.path.join(root, e["path"])):
        print("MISSING (fenced)", e["path"]); bad += 1
    elif sha(e["path"]) != e["sha256"]:
        print("CHANGED (fenced)", e["path"]); bad += 1
# import closure of BGL/Frozen
def mod_to_path(m):
    return m.replace(".", "/") + ".lean"
def imports(path):
    out = []
    for line in open(os.path.join(root, path)):
        mm = re.match(r"import\s+(MarkovTriple\.\S+)", line)
        if mm: out.append(mod_to_path(mm.group(1)))
    return out
seen = set()
stack = [p for p in listed if p.startswith("MarkovTriple/BGL/Frozen/")]
while stack:
    p = stack.pop()
    if p in seen: continue
    seen.add(p)
    if os.path.exists(os.path.join(root, p)):
        stack.extend(imports(p))
for p in sorted(seen):
    if p not in listed:
        print("UNFENCED dependency of the frozen surface:", p); bad += 1
print("OK" if not bad else "FAILED"); sys.exit(1 if bad else 0)
