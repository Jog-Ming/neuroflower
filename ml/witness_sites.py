"""Mine explicit generic type arguments from the ground-truth tree.

For the repair model the label is: did the original source print explicit type
arguments at this call? This script finds those sites in the ground-truth
sources and summarizes their shape (which methods, which argument forms), and
counts how many of them our decompiled tree prints without the witness.
Standard library only.
"""
import os
import re
import sys
from collections import Counter

WITNESS = re.compile(r"\.<([^<>]*(?:<[^<>]*>[^<>]*)*)>\s*([A-Za-z_$][\w$]*)\s*\(")
DIAMOND = re.compile(r"\bnew\s+[A-Z][\w.$]*\s*<\s*>\s*\(")


def files(root):
    for base, _, names in os.walk(root):
        for name in names:
            if name.endswith(".java"):
                yield os.path.join(base, name)


def ours_for(relative, tree):
    return os.path.join(tree, "src", relative)


def main(ground_truth, tree):
    total = witnesses = diamonds = 0
    by_method = Counter()
    missing = []
    for path in files(ground_truth):
        relative = os.path.relpath(path, ground_truth)
        total += 1
        with open(path, encoding="utf-8", errors="replace") as handle:
            text = handle.read()
        sites = [(m.start(), m.group(1), m.group(2)) for m in WITNESS.finditer(text)]
        diamonds += len(DIAMOND.findall(text))
        companions = None
        for offset, witness, method in sites:
            witnesses += 1
            by_method[method] += 1
            if tree:
                if companions is None:
                    ours_path = ours_for(relative, tree)
                    companions = ""
                    if os.path.exists(ours_path):
                        with open(ours_path, encoding="utf-8", errors="replace") as handle:
                            companions = handle.read()
                if companions and not re.search(
                        r"\.<[^>]*>\s*" + re.escape(method) + r"\s*\(", companions):
                    missing.append((relative, text.count("\n", 0, offset) + 1, method, witness[:40]))
    print(f"ground-truth files {total}: explicit witnesses {witnesses}, diamonds {diamonds}")
    print("top methods with witnesses:")
    for name, count in by_method.most_common(15):
        print(f"  {count:4d}  {name}")
    if tree:
        print(f"witnesses our tree lacks near the same file: {len(missing)}")
        for row in missing[:10]:
            print("   ", row)
    return witnesses, missing


if __name__ == "__main__":
    gt = sys.argv[1] if len(sys.argv) > 1 else "C:/Users/Jog_M/Programming/Minecraft-1.21.11/src/main/java"
    tree = sys.argv[2] if len(sys.argv) > 2 else None
    main(gt, tree)
