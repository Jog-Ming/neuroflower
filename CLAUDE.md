# neuroflower

The Vineflower fork and its experimental pipeline. This file holds only conventions that outlive any
particular stage; project facts — numbers, commands, file paths, the current objective and where the
work stands — belong in project memory.

## Rules

- **Never write bytecode.** No class-file writer, no post-processing of compiled classes. Every repair
  is a source edit, and the final bytes come from javac. Comparison tools may only read.
- **Never hand-edit the generated tree.** Repairs belong in the decompiler or in a deterministic
  post-pass that runs on every decompile. Editing the output tree by hand makes the result
  LLM-in-the-loop decompilation and cannot be reproduced from the jar.
- **The verifier is the only judge.** A repair counts when the verifier says the bytes match; no other
  argument, however convincing, is evidence.
- **Measure every change.** Score the tree before and after; restore what a rewrite got wrong before
  trusting it.
- **Never `sleep` to wait.** Poll a command with a bounded number of attempts and a timeout; never a
  blind `sleep N` before a check.
- **Read the ground truth before deriving a repair.** When a reference source tree is available, copy
  the form from it instead of re-deriving it from bytecode.
- **Verify before inventing.** A repair to one declaration is often illegal in terms of another
  (overrides, erasure, raw types). Diff the set of error messages between rounds.

## Naming

Modules carry both a neural and a botanical meaning where such a word exists (`amygdala`, `cortex`,
`hippocampus`; `dendron`, `auxin`, `meristem`).
