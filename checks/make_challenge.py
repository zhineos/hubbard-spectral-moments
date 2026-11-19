"""Regenerate lean/Challenge.lean, the reference statements for `lake comparator`.

Run from the repository root:

    python checks/make_challenge.py            # rewrite lean/Challenge.lean
    python checks/make_challenge.py --check    # exit 1 if lean/Challenge.lean is not up to date

The rule is the one stated in Challenge.lean's own docstring: its fixed header (everything up
to and including `namespace HubbardMoments`), then one line
`theorem <name> : Spec.<Prop> := sorry` for each theorem `theorem <name> : Spec.<Prop> := ...`
of lean/HubbardMoments/Main.lean, in the same order and separated by blank lines, then
`end HubbardMoments`. The header is taken from the existing file, so editing its docstring
is the only change made by hand.

Applied to the v1.0.0 Main.lean and Challenge.lean, this rule reproduces the released
Challenge.lean byte for byte.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAIN = ROOT / "lean" / "HubbardMoments" / "Main.lean"
CHALLENGE = ROOT / "lean" / "Challenge.lean"
MARK = "namespace HubbardMoments\n"


def generate(main_text: str, challenge_text: str) -> str:
    header = challenge_text[: challenge_text.index(MARK) + len(MARK)]
    theorems = re.findall(r"^theorem (\w+) : (Spec\.\w+) :=", main_text, re.M)
    if not theorems:
        raise SystemExit("no `theorem <name> : Spec.<Prop> :=` line found in Main.lean")
    body = "".join(f"\ntheorem {name} : {prop} := sorry\n" for name, prop in theorems)
    return header + body + "\nend HubbardMoments\n"


def main() -> int:
    current = CHALLENGE.read_text(encoding="utf-8")
    new = generate(MAIN.read_text(encoding="utf-8"), current)
    if "--check" in sys.argv[1:]:
        if new == current:
            print("lean/Challenge.lean is up to date")
            return 0
        print("lean/Challenge.lean is out of date: run python checks/make_challenge.py")
        return 1
    CHALLENGE.write_text(new, encoding="utf-8")
    n = new.count(":= sorry")
    print(f"wrote lean/Challenge.lean ({n} theorems)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
