"""Train the line-start model on the exported alignment dataset.

Each dataset line is one method: `ops` names every instruction, `ours` and
`target` give the source lines both sides attribute to it. The label of a
boundary is whether the target starts a new line there. The model is a sparse
logistic regression trained with plain SGD; no third-party packages, CPU only.
Weights are written as TSV so the fork can load them without a JSON library.
"""
import json
import sys
from collections import defaultdict

LEARNING_RATE = 0.1
EPOCHS = 3


def category(op):
    """Coarse instruction category from an operand string ('op:25' or a name)."""
    if op.startswith("op:"):
        try:
            code = int(op[3:])
        except ValueError:
            return "op"
        if 172 <= code <= 177:
            return "return"
        if 153 <= code <= 166 or code in (167, 198, 199):
            return "branch"
        if 59 <= code <= 81 or 182 <= code <= 195:
            return "invoke/new"
        if 178 <= code <= 181:
            return "field"
        if 21 <= code <= 53:
            return "var"
        if 2 <= code <= 15 or code == 18 or code == 20:
            return "const"
        if 83 <= code <= 132:
            return "array"
        return "op"
    if op.startswith("type:"):
        return "type"
    if op.startswith("const:"):
        return "const"
    return "name"


def features(prev, cur, index, length, run):
    p, c = category(prev), category(cur)
    bucket = min(7, index * 8 // max(1, length))
    run_bucket = min(3, run)
    return [f"bias", f"p:{p}", f"c:{c}", f"pc:{p}|{c}", f"i:{bucket}", f"r:{run_bucket}"]


def boundaries(method):
    ours, target, ops = method["ours"], method["target"], method["ops"]
    run = 0
    for i in range(1, len(target)):
        # The run is counted on OUR printed lines, which inference can see; the target only
        # supplies the label.
        if ours[i] == ours[i - 1]:
            run += 1
        else:
            run = 0
        label = 1.0 if target[i] != target[i - 1] else 0.0
        yield features(ops[i - 1], ops[i], i, len(target), run), label


def split(paths, holdout_every=10):
    """Streams the dataset; every tenth method is held out."""
    for path in paths:
        with open(path, encoding="utf-8") as handle:
            for index, line in enumerate(handle):
                yield index % holdout_every == 0, json.loads(line)


def sigmoid(z):
    if z < -30:
        return 0.0
    if z > 30:
        return 1.0
    return 1.0 / (1.0 + 2.718281828459045 ** -z)


def score(weights, method):
    tp = fp = tn = fn = 0
    for keys, label in boundaries(method):
        z = sum(weights.get(k, 0.0) for k in keys)
        predicted = 1 if z > 0 else 0
        if predicted and label:
            tp += 1
        elif predicted:
            fp += 1
        elif label:
            fn += 1
        else:
            tn += 1
    return tp, fp, tn, fn


def main(paths):
    weights = defaultdict(float)
    seen = 0
    for holdout, method in split(paths):
        if holdout:
            continue
        seen += 1
        for keys, label in boundaries(method):
            z = sum(weights.get(k, 0.0) for k in keys)
            error = sigmoid(z) - label
            for key in keys:
                weights[key] -= LEARNING_RATE * error
    print(f"trained on {seen} methods, {len(weights)} weights")

    tp = fp = tn = fn = 0
    held = 0
    for holdout, method in split(paths):
        if not holdout:
            continue
        held += 1
        a, b, c, d = score(weights, method)
        tp, fp, tn, fn = tp + a, fp + b, tn + c, fn + d
    precision = tp / max(1, tp + fp)
    recall = tp / max(1, tp + fn)
    accuracy = (tp + tn) / max(1, tp + tn + fp + fn)
    print(f"held-out {held} methods: accuracy {accuracy:.3f} precision {precision:.3f} recall {recall:.3f}")
    print(f"positives {tp + fn}, predicted {tp + fp}")

    out = "ml/weights/linebreak.tsv"
    with open(out, "w", encoding="utf-8") as handle:
        for key in sorted(weights):
            handle.write(f"{key}\t{weights[key]:.6f}\n")
    print(f"wrote {out}")


if __name__ == "__main__":
    main(sys.argv[1:] or [".dev/datasets/1.21.11_unobfuscated-methods.jsonl"])
