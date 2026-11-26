#!/usr/bin/env python3
"""ast_equiv.py -- mechanical equivalence check between the original scripts and their packaged copies.

The packaged scripts differ from the originals only in (a) file names, (b) comments and docstrings,
(c) the text of printed messages (translated to English) and (d) file paths (made relative to the package
root). This tool checks that claim mechanically. For every pair (original, packaged) listed in a map file:

  1. both files are parsed with Python's own `ast` module;
  2. docstrings are removed (a bare string as the first statement of a module, class or function body);
  3. import aliases are normalised (`import m` is treated as `import m as m`), and the module renames
     declared in the map file are applied to the ORIGINAL tree. Only the name of the imported module is
     renamed, never the name it is bound to, so every use of the module inside the code is unchanged;
  4. every string constant is replaced by one fixed placeholder; this includes the literal parts of
     f-strings and f-string format specifications;
  5. `ast.dump()` of the two trees is compared. The two dumps must be identical.

Because the trees are then identical, the string constants of the two files correspond one to one in
traversal order. The tool lists every string constant whose text differs (old -> new) with its line numbers
and its syntactic role. A change is FLAGGED unless the string is used only as a message: an argument of
print(), the message argument of the scripts' local failure helper dur(), an argument of an exception
constructor, or the message part of an assert statement. Flagged roles include dictionary keys, subscripts,
comparisons (e.g. tests on sys.argv or on the output of a sub-process), assert conditions, file names and
paths, and format specifications. A changed format specification makes the check fail.

Usage (from the package root, with access to the original files):
  python3 tools/ast_equiv.py tools/equiv_map.json --orig-root DIR [--redact-prefix P] [--redact-word W ...]

--redact-prefix and --redact-word only affect what is printed (they mask a local directory prefix and
given words in the listing of old strings); the comparison itself uses the unmodified files.
Exit status: 0 if every pair is equivalent and no format specification changed, 1 otherwise.
"""
import argparse
import ast
import hashlib
import json
import os
import sys

PLACEHOLDER = "<STR>"


def sha256(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def strip_docstrings(tree):
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            body = node.body
            if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
                    and isinstance(body[0].value.value, str):
                node.body = body[1:]
    return tree


def normalise_imports(tree, renames):
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.asname is None:
                    alias.asname = alias.name
                alias.name = renames.get(alias.name, alias.name)
        elif isinstance(node, ast.ImportFrom) and node.module is not None:
            node.module = renames.get(node.module, node.module)
    return tree


def collect_strings(tree):
    """String constants in a fixed traversal order, each with its ancestor chain [(parent, field, index)]."""
    out = []

    def rec(node, chain):
        for field, value in ast.iter_fields(node):
            if isinstance(value, list):
                for i, item in enumerate(value):
                    if isinstance(item, ast.AST):
                        rec(item, chain + [(node, field, i)])
            elif isinstance(value, ast.AST):
                rec(value, chain + [(node, field, None)])
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            out.append((node, chain))

    rec(tree, [])
    return out


def callee_name(call):
    f = call.func
    if isinstance(f, ast.Name):
        return f.id
    if isinstance(f, ast.Attribute):
        return f.attr
    return "?"


def classify(chain):
    """Syntactic role of a string constant, from the innermost ancestor outwards."""
    for parent, field, idx in reversed(chain):
        if isinstance(parent, ast.FormattedValue) and field == "format_spec":
            return "FORMAT_SPEC"
        if isinstance(parent, ast.Dict):
            return "DICT_KEY" if field == "keys" else "DICT_VALUE"
        if isinstance(parent, ast.Subscript) and field == "slice":
            return "SUBSCRIPT"
        if isinstance(parent, ast.Compare):
            return "COMPARISON"
        if isinstance(parent, ast.Assert):
            return "ASSERT_TEST" if field == "test" else "MESSAGE"
        if isinstance(parent, ast.Call):
            if field == "func":
                return "CALL_TARGET"
            name = callee_name(parent)
            if name == "print":
                return "MESSAGE"
            if name == "dur":
                return "MESSAGE" if (field == "args" and idx == 1) else "CALL_ARG:dur(condition)"
            if name.endswith("Error") or name.endswith("Exception"):
                return "MESSAGE"
            return f"CALL_ARG:{name}"
        if isinstance(parent, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            return "ASSIGNMENT"
        if isinstance(parent, ast.Return):
            return "RETURN_VALUE"
    return "OTHER"


def prepare(path, renames=None):
    with open(path, encoding="utf-8") as fh:
        src = fh.read()
    tree = ast.parse(src)
    strip_docstrings(tree)
    normalise_imports(tree, renames or {})
    strings = collect_strings(tree)
    info = [(c.value, c.lineno, classify(chain)) for c, chain in strings]
    for c, _ in strings:
        c.value = PLACEHOLDER
    return ast.dump(tree, annotate_fields=True, include_attributes=False), info


def show(s, redact_prefix, redact_words):
    if redact_prefix:
        s = s.replace(redact_prefix, "<orig>/")
    for w in redact_words:
        s = s.replace(w, "<redacted>")
    return repr(s)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mapfile")
    ap.add_argument("--orig-root", required=True)
    ap.add_argument("--redact-prefix", default="")
    ap.add_argument("--redact-word", action="append", default=[])
    a = ap.parse_args()
    with open(a.mapfile, encoding="utf-8") as fh:
        entries = json.load(fh)
    ok_all = True
    n_pairs = n_new = n_ident = 0
    n_flag_total = 0
    for e in entries:
        pkg = e["package"]
        if e.get("original") is None:
            n_new += 1
            print(f"== {pkg}\n   NEW FILE (no original; not covered by this equivalence check)\n"
                  f"   sha256 package: {sha256(pkg)}\n")
            continue
        n_pairs += 1
        orig = os.path.join(a.orig_root, e["original"])
        renames = e.get("module_renames", {})
        h_o, h_p = sha256(orig), sha256(pkg)
        print(f"== {pkg}\n   original: <orig>/{e['original']}\n   sha256 original: {h_o}\n   sha256 package:  {h_p}")
        if renames:
            print(f"   declared module renames (import statements only): {renames}")
        if h_o == h_p:
            n_ident += 1
            print("   BYTE-IDENTICAL\n")
            continue
        d_o, s_o = prepare(orig, renames)
        d_p, s_p = prepare(pkg)
        same = d_o == d_p and len(s_o) == len(s_p)
        print(f"   AST after removing docstrings and masking string constants: {'IDENTICAL' if same else 'DIFFERENT'}")
        if not same:
            ok_all = False
            print("   -> equivalence NOT established for this file\n")
            continue
        changed = [(o, p) for o, p in zip(s_o, s_p) if o[0] != p[0]]
        flagged = 0
        fmt_changed = 0
        lines = []
        for (vo, lo, ro), (vp, lp, rp) in changed:
            flag = ro != "MESSAGE"
            flagged += flag
            fmt_changed += ro == "FORMAT_SPEC"
            lines.append(f"   [{lo:>4}->{lp:<4}] {ro:<28} {'FLAG ' if flag else '     '}"
                         f"{show(vo, a.redact_prefix, a.redact_word)} -> {show(vp, '', [])}")
        print(f"   string constants: {len(s_o)} in total, {len(changed)} changed, {flagged} of the changes flagged"
              f" (role other than MESSAGE), {fmt_changed} format specifications changed")
        for ln in lines:
            print(ln)
        if fmt_changed:
            ok_all = False
            print("   -> a format specification changed: equivalence NOT accepted")
        n_flag_total += flagged
        print()
    print(f"SUMMARY: {n_pairs} original/packaged pairs ({n_ident} byte-identical), {n_new} new files; "
          f"flagged string changes: {n_flag_total}; "
          f"{'ALL PAIRS EQUIVALENT' if ok_all else 'AT LEAST ONE PAIR NOT EQUIVALENT'}")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
