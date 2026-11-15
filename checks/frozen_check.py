"""Frozen claims: the register agrees with the freeze record and the drift log.

Run from the repository root:  python checks/frozen_check.py
Exit status 0 if every frozen row of docs/correspondence.tsv is what docs/frozen.tsv
recorded at the freeze, changed only by the entries of docs/drift-log.tsv (framework §6).

docs/frozen.tsv     one row per frozen claim: the claim fields as approved, the date and the
                    approver. Rows are only ever appended (a later freeze adds rows).
docs/drift-log.tsv  one row per approved change to a frozen claim: date, label, field, old
                    text, new text, reason, approver. Append-only; replayed in file order.

Both files are append-only; the pre-commit hook refuses a commit that deletes or edits a
line of either. The claim fields are kind, statement, tier, lean and relation; `source`
(line numbers, annex sections) may change without a drift entry. A drift entry may also
change `label` (a rename) or `status` (unfreezing), which then removes the row from the
frozen set.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTER = ROOT / "docs" / "correspondence.tsv"
FROZEN = ROOT / "docs" / "frozen.tsv"
DRIFT = ROOT / "docs" / "drift-log.tsv"

CLAIM_FIELDS = ("kind", "statement", "tier", "lean", "relation")
FROZEN_COLUMNS = ("label",) + CLAIM_FIELDS + ("frozen_on", "approved_by")
DRIFT_COLUMNS = ("date", "label", "field", "old", "new", "reason", "approved_by")


def read_tsv(path, columns=None):
    lines = path.read_text(encoding="utf-8").splitlines()
    header = lines[0].split("\t")
    if columns is not None and tuple(header) != columns:
        raise ValueError(f"{path.name}: header {header} is not {list(columns)}")
    rows = []
    for i, line in enumerate(lines[1:], start=2):
        cells = line.split("\t")
        if len(cells) != len(header):
            raise ValueError(f"{path.name}:{i}: {len(cells)} cells, expected {len(header)}")
        rows.append(dict(zip(header, cells)))
    return rows


def problems():
    """Every disagreement, as a list of strings (empty when all is well)."""
    register = {r["label"]: r for r in read_tsv(REGISTER)}
    expected = {}
    for r in read_tsv(FROZEN, FROZEN_COLUMNS):
        if r["label"] in expected:
            return [f"frozen.tsv: {r['label']} frozen twice"]
        expected[r["label"]] = {f: r[f] for f in CLAIM_FIELDS} | {"status": "frozen"}
    out = []
    for i, d in enumerate(read_tsv(DRIFT, DRIFT_COLUMNS), start=2):
        where = f"drift-log.tsv:{i} ({d['label']}, {d['field']})"
        rec = expected.get(d["label"])
        if rec is None:
            out.append(f"{where}: no frozen claim with this label")
            continue
        if not d["reason"] or not d["approved_by"]:
            out.append(f"{where}: reason and approver are required")
        if d["field"] == "label":
            if d["old"] != d["label"] or d["new"] in expected:
                out.append(f"{where}: bad rename {d['old']} -> {d['new']}")
                continue
            expected[d["new"]] = expected.pop(d["label"])
        elif d["field"] in CLAIM_FIELDS + ("status",):
            if rec[d["field"]] != d["old"]:
                out.append(f"{where}: 'old' is not the current frozen text")
            rec[d["field"]] = d["new"]
        else:
            out.append(f"{where}: unknown field")
    for label, rec in expected.items():
        if rec["status"] != "frozen":
            continue
        row = register.get(label)
        if row is None:
            out.append(f"{label}: frozen but missing from the register")
            continue
        for f in CLAIM_FIELDS + ("status",):
            if row[f] != rec[f]:
                out.append(f"{label}: register {f} differs from the frozen text plus drift log")
    for label, row in register.items():
        if row["status"] == "frozen" and expected.get(label, {}).get("status") != "frozen":
            out.append(f"{label}: status 'frozen' in the register but not in frozen.tsv")
    return out


def main():
    found = problems()
    for p in found:
        print("FAIL ", p)
    n = sum(1 for r in read_tsv(REGISTER) if r["status"] == "frozen")
    print(f"{n} frozen rows; {len(found)} problem(s)")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
