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
- **The decompile path never compiles.** Neither the `javac` binary nor the `javax.tools.JavaCompiler`
  API may be called while decompiling. A decompile is one Vineflower run plus deterministic passes
  that decide from the class file alone; compiling belongs to the verifier, and a repair that needs a
  compile to choose between candidates is a search loop, not a decompiler. Offline training and data
  export may compile — that is not the decompile path.
- **devtools is the experiment pipeline only.** It downloads, decompiles, scores, and exports the
  corpus and dataset. No decompilation logic lives there — no source rewriting, no line alignment, no
  cast or name selection; those belong in the fork. If a pass would change the generated source, it
  is decompiler code and moves into `src/org/jetbrains/java/decompiler`.
- **The verifier is the only judge.** A repair counts when the verifier says the bytes match; no other
  argument, however convincing, is evidence.
- **Measure every change A/B.** Score the whole tree before and after, compare the `index.tsv` lines,
  and revert a change that lowers any attribute. Restore what a rewrite got wrong before trusting it.
- **Decompiler options take a double dash.** Write `--line-align=0`, never `-line-align=0`: the
  console parser reads a single-dash argument as a three-letter short name, so `-line-align=0`
  silently becomes `--lin=-align=0` and the run measures the unchanged default. A single-dash A/B is
  an empty measurement.
- **A blocked class is reported with its token pair.** Never write it off as a decompiler limitation;
  record the exact tokens that diverge.
- **Never print an erased type.** A repair may print a type only when every type argument is recorded
  and nameable: no wildcard captures, no erased stand-ins, no unresolved type variables. If the only
  available type is an erasure, a capture, or an unknown, print nothing. A raw or erased type changes
  the generic shape and can alter inference elsewhere, so producing one is a bug even where it
  compiles and even if the tree score rises.
- **The compile gate is deterministic.** A file that fails to compile is repaired only by facts
  recorded in the class file or by static language rules — never by a model, and never by compiling
  candidates and keeping one. A repair that would need either is reported as blocked instead.
- **Never `sleep` to wait.** A long command is launched in the background and its completion
  notification is the wait; a short readiness check polls with a bounded number of attempts and a
  timeout. Never a blind `sleep N` before a check.
  - Wrong: `sleep 90; tail out.log` — pays the full delay even if the result appeared after 2 s.
  - Right: launch long work with `run_in_background` and continue when it reports completion; for a
    readiness check use `devtools/poll <seconds> <command>`, which exits the moment the command
    succeeds and 124 on timeout:
    `devtools/poll 90 grep -q '^fully' .dev/tmp/score.out && tail -5 .dev/tmp/score.out`. The elapsed
    time it prints calibrates the next timeout; any request over 300 s is capped at 300 s with a notice.
- **Read the ground truth before deriving a repair.** When a reference source tree is available, copy
  the form from it instead of re-deriving it from bytecode.
- **Verify before inventing.** A repair to one declaration is often illegal in terms of another
  (overrides, erasure, raw types). Diff the set of error messages between rounds.
- **Commits are unsigned; pushing is signed and only on request.** Commit with `git commit --no-gpg-sign`;
  do not change the git configuration. Push only when the user asks, re-signing the branch before
  the push.
- **When the deterministic routes look exhausted, dispatch research subagents.** A fresh agent with
  one narrow, evidence-driven question sees what the working context has stopped noticing; give it
  the files, the measurement, and what is already ruled out, and ask for concrete proposals with
  the evidence behind them.

## devtools/cli

The only entry point for the experiment pipeline. Each version runs in its own process and is
killed after `--timeout` minutes per version (default 15); its staging tree is discarded. Usage:

```
devtools/cli versions [--no-cache]                    list Mojang's versions
devtools/cli decompile <version> [--no-cache] [--threads N] [--only Class] [--options "..."] [--timeout minutes]
devtools/cli tree      <version> [--only Class]       print the cached tree path
devtools/cli score     <version> [<version>...] [--no-cache] [--only Class] [--threads N] [--json] [--jobs N] [--options "..."] [--timeout minutes]
devtools/cli corpus    <version> --ground-truth <dir> write the class-to-ground-truth corpus
devtools/cli dataset   <version>                      export per-instruction line alignment for the model
devtools/cli reports   [--version V] [--limit N]      list past scores
devtools/cli clean     [--trees] [--compile] [--downloads] [--all]
devtools/cli cache     [--measure]                    show cache usage; --measure sizes old trees once
```

Several versions in one `score` run concurrently, `--jobs` at a time (default 2), with the thread
count split across them; logs go to `.dev/tmp/score-<version>.out`. A single version is the normal
iteration loop; score the whole goal set only after a batch of large gains.

**Changing this interface means changing this block.** Any new, removed or renamed command, flag or
default must be reflected here in the same change; an out-of-date usage block is a broken interface.

## Naming

Modules carry both a neural and a botanical meaning where such a word exists (`amygdala`, `cortex`,
`hippocampus`; `dendron`, `auxin`, `meristem`).
