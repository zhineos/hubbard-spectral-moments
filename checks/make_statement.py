"""Regenerate the claims of STATEMENT.md from the register.

Run from the repository root:

    python checks/make_statement.py            # rewrite STATEMENT.md
    python checks/make_statement.py --check    # exit 1 if STATEMENT.md is not up to date

STATEMENT.md lists the frozen rows of docs/correspondence.tsv verbatim (their current text, which
checks/frozen_check.py ties to docs/frozen.tsv and docs/drift-log.tsv). Everything before the
first section heading (`## §`) is written by hand (conventions, tiers) and kept, except the
sentence that counts the frozen claims, which is regenerated. Each frozen row is printed as

    **`label`** (kind; tier T, RELATION; Lean: `a`, `b`)

    statement

in the order of docs/frozen.tsv, under the section of the paper it belongs to; non-claims go
under "§9 What is not claimed".
"""
import csv
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATEMENT = ROOT / "STATEMENT.md"
REGISTER = ROOT / "docs" / "correspondence.tsv"
FROZEN = ROOT / "docs" / "frozen.tsv"

SECTIONS = [  # (heading, label prefixes), in paper order
    ("§2 The two-particle benchmark", ("sec:benchmark",)),
    ("§5 The second moment at U → ∞", ("sec:mu2theorem", "sec:fermistats", "app:mu4fpc")),
    ("§6 Exchange in the fourth moment", ("sec:mu4exchange", "eq:alphaN", "eq:Aclosed", "app:mu4walks")),
    ("§7 Finite U", ("sec:SW",)),
    ("§8 Gauge response", ("sec:futurework", "eq:doublonSW", "eq:mu4flux")),
]
NONCLAIMS = "§9 What is not claimed"
COUNT = re.compile(r"the\s+\d+\s+principal claims,\s+frozen[^\[]*?changed since only through", re.S)


def rows(path):
    with open(path, encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE))


def section_of(row):
    if row["kind"] == "non-claim":
        return NONCLAIMS
    for heading, prefixes in SECTIONS:
        if row["label"].split("#")[0] in prefixes or row["label"].startswith(prefixes):
            return heading
    raise SystemExit(f"no section for {row['label']}")


def entry(row):
    head = f"**`{row['label']}`** ({row['kind']}; tier {row['tier']}, {row['relation']}"
    if row["lean"].strip():
        head += "; Lean: " + ", ".join(f"`{x.strip()}`" for x in row["lean"].split(";"))
    return head + ")\n\n" + row["statement"] + "\n"


def generate(current):
    register = {r["label"]: r for r in rows(REGISTER)}
    frozen = rows(FROZEN)
    order = [r["label"] for r in frozen if register[r["label"]]["status"] == "frozen"]
    dates = Counter(r["frozen_on"] for r in frozen if r["label"] in order)
    when = " and ".join(f"{k} on {d}" for d, k in sorted(dates.items()))
    count = (f"the\n{len(order)} principal claims, frozen on {next(iter(dates))} and changed since only through"
             if len(dates) == 1 else
             f"the\n{len(order)} principal claims, frozen in two steps ({when}), and\nchanged since only through")
    head = current[: current.index("\n## §") + 1]
    head = COUNT.sub(lambda m: count, head, count=1)
    groups = {h: [] for h, _ in SECTIONS}
    groups[NONCLAIMS] = []
    for label in order:
        groups[section_of(register[label])].append(entry(register[label]))
    body = "\n".join(f"## {h}\n\n" + "\n".join(items) for h, items in groups.items() if items)
    return head + body


def main():
    current = STATEMENT.read_text(encoding="utf-8")
    new = generate(current)
    if "--check" in sys.argv[1:]:
        print("STATEMENT.md is up to date" if new == current else
              "STATEMENT.md is out of date: run python checks/make_statement.py")
        return 0 if new == current else 1
    STATEMENT.write_text(new, encoding="utf-8")
    print(f"wrote STATEMENT.md ({new.count('**`')} claims)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
