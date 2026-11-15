# The zhineos research framework

How zhineos papers are stated, checked, written and published. It applies to
every zhineos repository, starting with the condensed-matter papers;
`hubbard-spectral-moments` is the first instance.

A zhineos paper's evidence is usually mixed: some results can be proved in
Lean, some are proved on paper only, and some are numerical. The framework
therefore gives every claim an explicit **evidence tier**.

## 1. Principles

1. **No claim is stronger than its evidence.** A statement may be weaker or
   more natural than what is proved, never stronger.
2. **Every claim has exactly one evidence tier** (section 2), and the paper
   says which.
3. **Say what is not claimed.** Every paper has a non-claims list. Open
   coefficients and numerical trends are labelled as such, never presented as
   theorems.
4. **Everything is pinned:** Lean toolchain, Mathlib commit, Python package
   versions, the git commit that links point to, and file hashes for released
   data.
5. **The writer does not judge.** Whoever drafts a statement or a proof does
   not review it. Reviewers work from the text and the sources, not from the
   writer's reasoning.
6. **Records are append-only.** Findings, decisions and evidence runs are
   added, never edited or deleted. Corrections are new entries.

## 2. Evidence tiers

| Tier | Meaning | Required evidence |
|---|---|---|
| **L** | Proved in Lean | Declaration name in `lean/`, passing the axiom audit (section 4) |
| **A** | Proved analytically, not machine-checked | Proof in the paper or an annex, with its address |
| **N** | Exact numerical result | Script, command, parameters and recorded output; exact rationals where possible |
| **E** | Numerical evidence or fit | As **N**, plus the tolerance or fit range; never called a theorem |
| **C** | Taken from the literature | Exact citation: name, hypotheses and equation number, checked against the source |

When a claim moves up a tier (A to L, for example), the claims register and
the paper are updated together, and the change goes in the drift log.

**Cross-checks between tiers.** An exact numerical table entry (**N**) that a
Lean or analytic formula also predicts is checked against that formula by
`checks/`. The formula and the computation then confirm each other.

## 3. Repository layout

```text
<repo>/
  README.md               the result in brief, what is not claimed, how to reproduce
  STATEMENT.md            the precise claims, conventions and non-claims, with the tier of each
  CHANGELOG.md            reader-facing record of releases and corrections
  CITATION.cff            citation metadata, including the pinned commit
  LICENSE                 Apache-2.0 for code and Lean
  requirements.txt, *.py  numerics
  checks/                 golden-value checks: paper numbers against scripts and formulas
  lean/                   the Lean project (section 4)
  evidence/
    YYYY-MM-DD-<what>/    dated run records: command, versions, commit, time, memory, hashes, result.json
  docs/
    framework.md          this document
    method.md             how the evidence was produced; what each check does and does not establish
    correspondence.tsv    paper label ↔ tier ↔ Lean declaration ↔ script ↔ status
    glossary.md           code names ↔ paper symbols
    provenance.md         what comes from prior work and what is new
    faq.md                questions about the result and its limits
  manuscript/             private until publication
  analytic_studies/       private until publication
  research_notebooks/     private, never published
  results/                generated outputs, never committed
```

**Public and private.** `STATEMENT.md`, `docs/correspondence.tsv` and the
Lean `Spec.lean` spell out the results, so they live on the private branch
`lean`, together with the paper and its Supplemental notes, until the preprint
is out; the research notebooks are on a separate private branch, `notebook`,
and are never published. `main` holds the code, the
framework and the reproduction instructions. The pre-push hook enforces this;
it does not travel with a clone and must be copied to every machine.

## 4. Lean conventions

- **Pinned:** `lean-toolchain` (exact Lean version), `lakefile.toml` (Mathlib
  pinned by commit) and `lake-manifest.json` are committed. Mathlib comes from
  `lake exe cache get` and is never rebuilt locally.
- **Statements are kept apart from proofs.**
  - `Spec.lean` imports only Mathlib. It states each claim as a `def … : Prop`
    whose docstring gives the paper label.
  - `Challenge.lean` restates the headline theorems with `sorry`, as the
    reference.
  - `Main.lean` proves them.
  - `lake comparator` (part of Lake since Lean v4.35.0; configuration in
    `comparator.json`) checks that each proof proves exactly the reference
    statement, uses only the permitted axioms, and is accepted by the kernel.
    With `--paranoid` it also runs the five external checkers bundled with
    Lean on the same export, which holds the headline theorems and everything
    they depend on. `lake check` replays the whole build through Lean's
    kernel; since the build imports all of Mathlib, its export is about 6 GB,
    so it runs without `--paranoid`.
- **Permitted axioms:** `propext`, `Classical.choice` and `Quot.sound` only.
  `AxiomAudit.lean` runs `#print axioms` on every headline theorem.
  `native_decide` is not used, because it adds a trusted-compiler axiom that
  the audit rejects.
- **Build hygiene:** zero warnings, and no `sorry` outside `Challenge.lean`.
- **Every file:**
  - starts with an SPDX license line;
  - has a `/-! … -/` header saying what it proves, where that sits in the
    paper, and what it does not cover;
  - sets `set_option autoImplicit false`;
  - uses Mathlib naming conventions.
- **No Lean names in the paper outside the machine-checked appendix.** The
  appendix lists each formal statement with its Lean theorem names, so that a
  reader can verify it; everywhere else the connection lives in
  `docs/correspondence.tsv`. (Changed 2026-11-14, review round 3.)
- **Negative controls** (added once the project is stable): a weakened
  statement, an added axiom and a changed definition must each be rejected by
  the checks.
- **Final run** on Linux, where `lake comparator` and `lake check` build and
  export the project inside their `bwrap` sandbox, recorded under
  `evidence/`. Development can happen on any machine.

## 5. Numerical conventions

- Every **N** or **E** claim names its script, command and parameters, and
  its expected value: exact, or a value plus a tolerance.
- `checks/` re-runs the fast cases and compares them with the numbers printed
  in the paper. Slow cases are covered by a dated evidence record instead.
- **Evidence records** (`evidence/YYYY-MM-DD-<what>/`) hold:
  - the date, machine, OS, and Python and package versions;
  - the git commit, the command, and the wall time and peak memory;
  - SHA-256 hashes of the outputs, and the logs.

  Old records are never overwritten.
- Generated results are never committed. At publication they are released as
  an archive with `SHA256SUMS` (on Zenodo, with a DOI).

## 6. The claims register (the spine)

Before any prose is revised, every claim of the paper is fixed in one table,
`docs/correspondence.tsv`:

| column | content |
|---|---|
| `label` | the LaTeX label (`thm:main`, `tab:exact`, …) |
| `kind` | theorem, proposition, formula, table entry, figure, non-claim |
| `statement` | the claim in natural form: at most 150 words, one idea, quantifiers first |
| `tier` | L, A, N, E or C |
| `lean` | Lean declaration(s), if tier L |
| `relation` | DIRECT, WEAKER, COMPOSITION, CITED or NONE: how the paper statement relates to the evidence |
| `source` | Lean `module:line`, annex section, or script and output |
| `status` | draft, checked or frozen |

- **Relations.** DIRECT: the evidence proves or computes the statement itself, or something more
  general from which it follows by specialization alone (a Lean theorem for every graph supports
  a statement on the torus directly). WEAKER: the evidence covers less than the statement says,
  which the framework does not allow for a claim, so a WEAKER row must be narrowed or relabelled
  before freezing. COMPOSITION: the statement follows from several pieces of evidence, at least one
  of a lower tier, combined by an argument stated in the source column. CITED: taken from the
  literature. NONE: a non-claim, which needs no evidence.
- **Freezing.** The author approves the principal claims, which are then
  frozen: their status becomes `frozen`, and `docs/frozen.tsv` records the
  approved kind, statement, tier, lean and relation.
- **Drift protocol.** A frozen claim changes only through a drift-log entry
  (old text, new text, reason) approved by the author, in
  `docs/drift-log.tsv`. Both files are append-only (the pre-commit hook
  refuses edits and deletions), and `checks/frozen_check.py` replays the log
  over the freeze record and compares the result with the register.
- **Clause map.** Every clause of every Lean headline theorem is assigned to a
  row, and every row of tier L points to declarations that the audit covers.

## 7. Writing rules for the paper

| rule | limit |
|---|---|
| theorem, proposition or lemma | about 100 words, at most 150 |
| definition | about 120 words, at most 200; given by a formula, with one sentence of purpose |
| ideas per statement | one; conditions go in the setup, not in the statement |
| references between numbered items | always `\ref`, never a typed number |
| code and Lean names, file paths | never in the main text; Lean names only in the machine-checked appendix, code and paths only in "Code and data availability" |
| standard results | cited exactly, checked against the source |
| numerical trends | labelled as numerical evidence, never as theorems |
| non-claims | a dedicated paragraph or section |

## 8. Roles and review cycle

| role | who | does |
|---|---|---|
| project lead | the author | approves the spine and every drift; reads each finished section; sets length and level |
| editor | Claude, main session | writes tasks, integrates text (the only one who edits the manuscript), runs the checks, keeps the records |
| reviewers | fresh-context agents | read a frozen snapshot and report; never edit |

**Cycle for each section:**

1. **Task:** contents, sources and page allowance.
2. **Draft or revision.**
3. **Integration**, then the automatic checks (below).
4. **Frozen snapshot**, with a SHA-256 manifest. A review verdict applies to
   that snapshot only.
5. **Reviews**, each by a separate reviewer:
   - **Statement owner:** reads the text in order up to the claim, then maps
     each clause to the spine and the evidence and tries to break it.
   - **Mathematical review:** checks every proof step against the Lean,
     annex or script. Is it correct, complete, and no stronger than what is
     proved?
   - **Fresh reader:** has no sources. Reports every place where they had to
     guess, and ends with a two-sentence summary that is compared with the
     intended content.
   - **Prose truth:** marks every explanatory sentence true, false or
     unsupported, with evidence.
6. **Response table:** one row per finding, with the decision (applied, or
   declined with a reason), the edit, and how it was checked.
7. **Re-check** by the same reviewers.
8. **Delivery review:** the PDF matches the sources, every finding is closed,
   and every reference resolves.

**Pilot first.** One section, and the Lean for its claim, go through the whole
cycle before the others start.

**Automatic checks**, run after every integration:

- LaTeX: 0 errors, no undefined references, no overfull lines, a clean BibTeX
  run;
- word counts of statements and definitions;
- vocabulary: no code names, file paths or process words in the text;
- correspondence: every Lean name exists and passes the axiom audit, and
  every script exists;
- `checks/` passes, including the frozen-claims check.

Passing them means none of these mechanical faults is present. It says nothing
about whether the mathematics is right.

**Limits.** AI reviewers are independent of the writer but not of each other's
training, so they can share blind spots. The author's own reading, and later
human referees, remain necessary.

## 9. Publication checklist

- [ ] Every row of `correspondence.tsv` is checked or frozen; no open findings.
- [ ] Lean: clean build, axiom audit, `lake comparator --paranoid`, the
      negative controls and `lake check` run on Linux
      (`checks/lean_linux_run.py --record`), evidence recorded.
- [ ] Numerics: `checks/` passes, the slow runs are recorded, and the results
      archive has `SHA256SUMS`.
- [ ] `STATEMENT.md`, `docs/method.md` (including a table of what each check
      does and does not establish), `faq.md`, `glossary.md` and
      `provenance.md` are written.
- [ ] Paper: a code-availability section citing the pinned commit; non-claims
      stated.
- [ ] Release: arXiv (upload the `.bbl`), a Zenodo DOI for the repository
      snapshot, `CITATION.cff`, `LICENSE`, and a `CHANGELOG.md` entry.
- [ ] The publishable parts of the private branch `lean` are copied into
      `main`, and the pre-push hook is relaxed for the released folders.

## 10. Applying the framework to a repository

Each repository keeps its own plan (claims, current tiers, target tiers,
order of work) with its private material until publication, because the plan
names the results. For `hubbard-spectral-moments` it is `lean/PLAN.md`.

The order of work is the same everywhere:

1. Write the spine (`docs/correspondence.tsv`) from the paper's abstract and
   tables.
2. Pilot: one headline claim in Lean, plus its paper section through the full
   review cycle.
3. The remaining tier-L targets.
4. `checks/` and the evidence records.
5. The public documents.
