#!/usr/bin/env python3
"""json_equiv.py -- check that the packaged certificate files carry the same data as the original files.

For every pair (original, packaged) listed in the map file:
  * if the two files are byte-identical, this is reported (all S certificates are shipped byte-identical; this
    matters because the C and R certificates bind their S certificate by SHA-256);
  * otherwise both files are parsed as JSON and compared key by key; every top-level key whose value differs is
    listed, and the pair is accepted only if all differing keys belong to the set declared for that pair in the map
    (here: the path field "u1_sertifika" of the C/R certificates, which the verifiers resolve relative to the package
    root, and the free-text field "aciklama" of the overflow counterexample, which contained internal labels in the original).
Usage (from the package root, with access to the original files):
  python3 tools/json_equiv.py tools/json_map.json --orig-root DIR [--redact-prefix P] [--redact-word W ...]
--redact-prefix / --redact-word only mask a local directory prefix and given words in the printed listing.
"""
import argparse
import hashlib
import json
import os
import sys


def sha256(p):
    with open(p, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mapfile")
    ap.add_argument("--orig-root", required=True)
    ap.add_argument("--redact-prefix", default="")
    ap.add_argument("--redact-word", action="append", default=[])
    a = ap.parse_args()
    entries = json.load(open(a.mapfile, encoding="utf-8"))
    ok_all = True
    n_ident = 0
    for e in entries:
        po, pp = os.path.join(a.orig_root, e["original"]), e["package"]
        ho, hp = sha256(po), sha256(pp)
        print(f"== {pp}\n   original: <orig>/{e['original']}\n   sha256 original: {ho}\n   sha256 package:  {hp}")
        if ho == hp:
            n_ident += 1
            print("   BYTE-IDENTICAL\n")
            continue
        do, dp = json.load(open(po, encoding="utf-8")), json.load(open(pp, encoding="utf-8"))
        keys = sorted(set(do) | set(dp))
        diff = [k for k in keys if do.get(k, "<absent>") != dp.get(k, "<absent>")]
        allowed = set(e.get("allowed_changes", []))
        ok = set(diff) <= allowed
        ok_all &= ok
        for k in diff:
            vo = str(do.get(k, "<absent>"))
            if a.redact_prefix:
                vo = vo.replace(a.redact_prefix, "<orig>/")
            for w in a.redact_word:
                vo = vo.replace(w, "<redacted>")
            print(f"   key {k!r} differs ({'declared' if k in allowed else 'NOT DECLARED'}):\n"
                  f"      original: {vo!r}\n      package:  {str(dp.get(k, '<absent>'))!r}")
        print(f"   all other keys identical ({len(keys) - len(diff)} keys): {'ACCEPTED' if ok else 'NOT ACCEPTED'}\n")
    print(f"SUMMARY: {len(entries)} files, {n_ident} byte-identical; "
          f"{'ALL ACCEPTED' if ok_all else 'AT LEAST ONE FILE NOT ACCEPTED'}")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
