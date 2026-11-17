# Method

How the evidence for each claim of the paper was produced, and what each check does and does
not establish. The rules behind it are in [`framework.md`](framework.md); the claims are in
[`../STATEMENT.md`](../STATEMENT.md) and, with their evidence, in
[`correspondence.tsv`](correspondence.tsv).

## Kinds of evidence

Every claim carries one tier, and no claim is stated more strongly than its evidence.

- **L, machine-checked.** The statement is a proposition in `lean/HubbardMoments/Spec.lean`,
  written with Mathlib and the definitions of `Defs.lean` only, so it can be read without the
  proofs; `Main.lean` proves it. The projected operator $H_\infty$ is built there from fermion
  operators that satisfy the canonical anticommutation relations, for any ordering of the
  orbitals.
- **A, analytic.** A complete derivation in the Supplemental Material (notes S1–S11,
  `analytic_studies/`), checked by reviewers step by step and, wherever a number can be
  computed, against exact evaluation.
- **N, exact numerics.** Recomputed by `checks/` from the repository's code: exact rationals
  where the traces are integers (zero flux, $\lambda=1$), otherwise with a stated tolerance.
- **E, numerical evidence.** A trend seen in exact numbers over a finite set of sizes; it is not
  a proof and is labelled as such in the paper.
- **C, literature.** An exact citation, checked against the source.

## What each check does and does not establish

| check | establishes | does not establish |
|---|---|---|
| `lake build` (0 warnings) and `lake env lean AxiomAudit.lean` | every headline theorem compiles and depends only on `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no trusted compiled code | that the Lean statement says what the paper says; that is checked by the reviewers and recorded in `correspondence.tsv` |
| `lake comparator --paranoid` | each of the 46 proofs proves exactly the statement of `Challenge.lean`, with only the permitted axioms, accepted by six independent kernels (Lean's default and paranoid checkers, lean4lean, nanoda, con-leche, con-ron) | that `Challenge.lean` matches the paper; it is generated from `Main.lean`, so it guards the proofs, not the statements |
| four negative controls | the comparator rejects a weakened statement, an added axiom, a changed definition and an unproved step | that every possible error would be caught |
| `lake check` | the whole default build, with all of Mathlib, replays through Lean's kernel from an export | anything about the statements |
| `checks/run_checks.py` (176 checks, about 2 minutes) | every number of the paper that has a check equals an independent computation, and each closed form equals the exact values it predicts at the sizes computed | a statement for sizes, graphs or fillings that were not computed; agreement of two codes written by the same authors is not independent proof |
| `checks/frozen_check.py` (run inside `run_checks.py`) | the frozen claims in the register are exactly the freeze record plus the approved changes of the drift log; a tampered line is caught | that the claims are true |
| slow runs (`checks/slow_*.py`, `evidence/`) | the larger computations behind specific numbers, recorded with command, versions, commit, time, memory and checksums | anything beyond those numbers |
| figure records (e.g. `evidence/2026-11-14-fig-sectors`) | which code and inputs produced a figure, with its checksum | that the figure is the only possible reading of the data |
| reviews (below) | that independent readers checked the statements, proofs and prose against the sources and found no remaining error | that no error remains: reviewers can share blind spots |

## Run records

`evidence/<date>-<what>/` holds one run each: `command.txt`, `environment.json` (versions,
machine, commit, whether the tree was clean), `result.json`, logs, and `SHA256SUMS`. A record
from a tree with uncommitted changes is marked as such and is not final evidence. Failed runs
are kept: `evidence/2026-11-13-lean-linux` failed because of faulty memory on the Linux machine
(single bits flipped in cached Mathlib files, while the files on disk were intact); after the
memory was replaced, `evidence/2026-11-14-lean-linux` passed all ten steps from the same commit.

The commits named in the records (`git_commit` in `environment.json`) belong to the
development history before the first release, which is not public, so they cannot be checked
out from this repository. For each record, the author compared the files it ran (the script
and the repository modules it imports; for the Lean runs, `lean/` and
`checks/lean_linux_run.py`) with the same files in release v1.0.0:

| record | the code it ran, against v1.0.0 |
|---|---|
| `2026-11-13-finite-U`, `2026-11-14-alpha-c2`, `2026-11-14-lean-linux-2` | identical (for `lean-linux-2`, every released file of `lean/` except `lean/README.md`, edited after the run) |
| `2026-11-13-n6-linearity` | identical, except that two functions this run does not use (`four_cycles`, `small_graphs`) were added to `checks/hinf_local.py` afterwards |
| `2026-11-14-fig-sectors` | identical code; only the docstring of `fig_sectors.py` was edited afterwards |
| `2026-11-13-alpha-c2` | an earlier `checks/slow_alpha_c2.py`, without the $L=6$ case; superseded by `2026-11-14-alpha-c2` |
| `2026-11-13-lean-linux`, `2026-11-14-lean-linux` | differs in a section number inside a comment of `lean/HubbardMoments/Spec.lean` and in how `checks/lean_linux_run.py` names a second record of the same day; superseded by `2026-11-14-lean-linux-2` |
| `2026-11-12-finite-U`, `2026-11-12-n6-linearity` | scripts not yet committed (the tree was not clean); superseded by the 2026-11-13 records |
| `2026-11-12-n3-bound-states` | a script not yet committed (the tree was not clean); this is the only record of `sec:n3test#unbound` |

## Reviews

Claims were reviewed in rounds, each on a frozen snapshot of the paper and sources identified by
a SHA-256 manifest, by reviewers who had not written the material:

- **statement owner and mathematical review** of each principal claim (rounds 1 and 2, and a
  re-check of every claim edited afterwards);
- **fresh reader**, with the paper only, listing every place a reader has to guess;
- **prose truth**, marking every explanatory sentence true, false or unsupported, with evidence;
- a **re-check** by the same reviewers after each revision, and a **delivery review** that the
  PDF matches the sources, every finding is closed and every reference resolves.

Each finding is answered in a response table (applied, or declined with a reason). The
reviewers were AI models (Claude, Anthropic; GPT models from OpenAI also reviewed the
statements), independent of the writer but not of each other's training; the author's own
reading and the journal's referees remain necessary.

## Reproducing

See the repository README for the environment. Then, from the repository root:

```sh
python checks/run_checks.py                 # golden values and the register (about 2 minutes)
python checks/lean_linux_run.py --record    # Linux only: build, audit, comparator, controls, lake check
```

and, for the slow runs, the commands in `checks/README.md`.
