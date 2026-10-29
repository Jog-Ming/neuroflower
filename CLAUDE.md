Your usage is unlimited. Do not be sparing with tokens — spend them freely and without hesitation.
Remember this always: you are very rich.

# neuroflower

The Vineflower fork and its experimental pipeline. This file may hold whatever a session needs to
work correctly — conventions, the pipeline's interface, current facts, numbers and paths — and it is
allowed to change as the work does.

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
- **Decompiler options take a double dash.** Write `--rt-off=elseflat`, never `-rt-off=elseflat`:
  the console parser reads a single-dash argument as a three-letter short name, so `-rt-off=elseflat`
  silently becomes `--rt-=ff=elseflat` and the run measures the unchanged default. A single-dash A/B
  is an empty measurement.
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
  the form from it instead of re-deriving it from bytecode — and understand why that form is right,
  not just what it says.
- **Commits are unsigned; pushing is signed and only on request.** Commit with `git commit --no-gpg-sign`;
  do not change the git configuration. Push only when the user asks, re-signing the branch before
  the push.
- **History is only ever appended.** A subagent may commit its own verified change and may revert its
  own uncommitted edit with `git checkout -- <path>`; it may not rebase, reset, amend, force-push or
  touch another agent's commit. Signing rewrites history in the main process, and it happens only
  when the user asks for a push — never while an agent is working, because a working tree with
  uncommitted edits cannot be rebased safely.
- **Measurement happens in the main checkout, never in a worktree.** The devtools caches are shared
  state under `.dev/`; a decompile or score run inside a second checkout builds its own tree and
  compile caches from scratch and its numbers are not comparable with the ones in the reports. To
  read an earlier revision of a file, use `git show <rev>:<path>`; to measure a variant, edit the
  main working tree, measure, and revert with `git checkout -- <path>`.
- **A subagent's tool calls never prompt the user for approval.** A wave of agents that each stop on a
  permission dialog buries the user. The brief must name only paths and commands the agent can run
  without a prompt — reading, grepping, the project's own scripts under `.dev/tmp` — and must state
  that a step which would need approval is skipped and written into the report instead of attempted.
  Message a running agent this rule the moment it is added.
## The family loop

Every unaligned metric is worked the same way. The main process classifies and dispatches; it does
not edit decompiler code. The one exception is devtools itself: when the user asks for a change to
the pipeline — a new subcommand, a flag — the main process makes it directly. That is a tool the
loop runs on, not a repair, and the family rules do not apply to it.

1. **Classify.** Split the metric's residue into families by root cause, not by first opcode: a
   shared first-divergence instruction is a starting guess that the research step has to confirm or
   dissolve. Count per method, not per file — a file-level tally picks up a sibling class's
   difference and inflates a family several-fold.
   **The classification is a hypothesis, and a wrong one is the normal case.** The research agent
   must be free to answer "this is not one family" or "this family has no members left": the first
   survey's buckets were wrong about half the time (a supposed 72-class continue-guard family was 6;
   a 41-class constant family could not exist, because javac inlines those constants). A research
   report that dissolves a family is a success, and the next round re-cuts the residue with what it
   learned.
2. **Research one family.** Give a fresh agent one family, the report, our tree and the
   ground-truth tree. It picks one or more representative classes — as short as possible, and free of
   other families' or metrics' problems — and works out the repair by hand, editing a scratch copy of
   the *tree* to prove the form; when no such class exists it decompiles one it writes itself. It may
   use devtools **one class at a time** (`decompile <version> --only <Class>`, `score <version>
   --only <Class>`, `tree <version> --only <Class>`), never a whole-tree score and never a build: a
   rebuilt jar in the middle of a full measurement makes classes vanish from it. It must explain why
   the ground truth is right, and offer at least one candidate repair that differs from the ground
   truth and say what separates them in the class file — that is the proof it understood the shape
   rather than copied it.
3. **Implement one family, with devtools.** A different agent applies the agreed rule to the whole
   family, runs the whole-tree regression and commits only when no attribute drops. devtools takes
   concurrent calls — trees and compile output are content-addressed, writes are atomic and pruning
   holds a file lock and skips trees in use — so research agents may call it in parallel. What must
   not overlap is a **build**: the jar is the measurement's input, and rebuilding it mid-run makes
   classes vanish. One implementation agent owns the build at a time.
4. **Repeat** until the metric has no family left. A family with no deterministic discriminator is
   reported as blocked, and the report **records the exact diverging token pair** and which piece of
   evidence is missing, so the next round starts from that record instead of re-deriving it. The
   token pair is what makes a blocked family actionable later; "the decompiler cannot do this" is
   not a report.

## devtools/cli

The only entry point for the experiment pipeline. Each version runs in its own process and is
killed after `--timeout` minutes per version (default 15); its staging tree is discarded. Usage:

```
devtools/cli versions [--no-cache]                    list Mojang's versions
devtools/cli decompile <version> [--no-cache] [--threads N] [--only Class] [--options "..."] [--timeout minutes]
devtools/cli tree      <version> [--only Class]       print the cached tree path
devtools/cli score     <version> [<version>...] [--no-cache] [--only Class] [--threads N] [--json] [--options "..."] [--timeout minutes] [--since Tree]
devtools/cli diff      <version> <Class> [<Class>...]  verify classes and explain every failing attribute
devtools/cli compile   <version> <Class>             compile that one class like the verifier does
devtools/cli corpus    <version> --ground-truth <dir> write the class-to-ground-truth corpus
devtools/cli dataset   <version>                      export per-instruction line alignment for the model
devtools/cli reports   [--version V] [--limit N]      list past scores
devtools/cli clean     [--trees] [--compile] [--downloads] [--all]
devtools/cli cache     [--measure]                    show cache usage; --measure sizes old trees once
```

Several versions in one `score` run are scored one after another — there is no concurrency
switch, because two decompiles beside the verifier's javac exhaust this machine's page file
(measured: the second JVM died at startup with `os::commit_memory ... the paging file is too
small`); logs go to `.dev/tmp/score-<version>.out`. A single version is the normal iteration
loop; score the whole goal set only after a batch of large gains.

**Changing this interface means changing this block.** Any new, removed or renamed command, flag or
default must be reflected here in the same change; an out-of-date usage block is a broken interface.

`DEVTOOLS_NO_BUILD=1` skips the decompiler-jar freshness check, which every command otherwise runs.
A read-only caller — a research agent compiling one class with the verifier's javac — sets it so a
compile never rebuilds the jar a measuring agent is using: `DEVTOOLS_NO_BUILD=1 devtools/cli compile
<version> <Class>`. It is never set for a command whose result is a measurement.

**One devtools command at a time inside a process tree.** A background `score` running while another
call rebuilds the jar gives `NoClassDefFoundError` and caches a broken tree; the rebuild is only
serialised against other *builds*, not against a decompile already in flight.

**Never call the jar or a compiler directly.** `java -jar build/libs/…`, `javac`, and any other raw
tool invocation prompt the user for approval, and a subagent's tool calls must never do that. Go
through the subcommands: `compile` for one class with the verifier's javac, `decompile --only` for
one class's source, `diff` for verification. A debugging environment variable is still fine — it is
inherited by the child process: `DEVTOOLS_NO_BUILD=1 NF_TRACE_IF=1 devtools/cli decompile …`.

