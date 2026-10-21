"""Mine the edits that make a failing decompiled file compile.

Reads the repair corpus manifest (devtools/cli corpus), aligns each failing
file against its ground-truth source, and summarizes the token edits found
around each compile error. Standard library only; nothing here runs in the
decompile path.
"""
import difflib
import json
import os
import re
import sys
from collections import Counter, defaultdict

PADDING = "// line-number padding"
TOKEN = re.compile(r"[A-Za-z_$][\w$]*|\d+(?:\.\d+)?|::|->|<>|[^\s\w$]")


def code_lines(path):
    with open(path, encoding="utf-8", errors="replace") as handle:
        return [line for line in handle.read().split("\n") if PADDING not in line]


def tokens(text):
    return TOKEN.findall(text)


def edit_kind(ours, target):
    """Classify how the ground truth differs from our tokens."""
    a, b = tokens(ours), tokens(target)
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    ops = [op for op in sm.get_opcodes() if op[0] != "equal"]
    if not ops:
        return "text-same"
    inserted = []
    deleted = []
    for tag, i1, i2, j1, j2 in ops:
        inserted += b[j1:j2]
        deleted += a[i1:i2]
        if tag == "insert" and b[j1:j2] == ["<", ">"]:
            return "insert-diamond"
    ins = " ".join(inserted)
    dele = " ".join(deleted)
    if re.fullmatch(r"\(\s*[\w.$<>,\[\] ]+\s*\)", ins.strip()):
        return "insert-cast"
    if ins and not dele:
        return "insert " + (ins[:40])
    if dele and not ins:
        return "delete " + (dele[:40])
    if ins and dele:
        return "replace " + (dele[:30] + " -> " + ins[:30]).strip()
    return "other"


def error_lines(errors):
    lines = []
    for error in errors:
        match = re.match(r"(\d+):", error)
        if match:
            lines.append(int(match.group(1)))
    return lines


def main(manifest_paths):
    counts = Counter()
    examples = defaultdict(list)
    for manifest_path in manifest_paths:
        with open(manifest_path, encoding="utf-8") as handle:
            for raw in handle:
                entry = json.loads(raw)
                if not entry.get("errors"):
                    continue
                ours_path, target_path = entry.get("source"), entry.get("target")
                if not ours_path or not target_path or not os.path.exists(ours_path) or not os.path.exists(target_path):
                    continue
                ours, target = code_lines(ours_path), code_lines(target_path)
                matcher = difflib.SequenceMatcher(None, [l.strip() for l in ours],
                                                  [l.strip() for l in target], autojunk=False)
                opcodes = matcher.get_opcodes()
                for line in error_lines(entry["errors"]):
                    if not (1 <= line <= len(ours)):
                        continue
                    for tag, i1, i2, j1, j2 in opcodes:
                        if tag == "equal" or not (i1 < line <= i2 or (i1 == i2 == line - 1)):
                            continue
                        kind = edit_kind("\n".join(ours[i1:i2]), "\n".join(target[j1:j2]))
                        counts[kind] += 1
                        if len(examples[kind]) < 3:
                            examples[kind].append((entry["class"], line, entry["errors"][0][:80]))
                        break
    print("edit patterns near compile errors:")
    for kind, count in counts.most_common(25):
        print(f"{count:5d}  {kind}")
        for cls, line, err in examples[kind][:2]:
            print(f"        {cls}:{line}  {err}")
    return counts


if __name__ == "__main__":
    main(sys.argv[1:])
