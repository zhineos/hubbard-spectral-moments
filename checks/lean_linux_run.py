"""The final Lean run (docs/framework.md §4, §9): clean build, axiom audit, `lake comparator`,
`lake check`, the negative controls and the numerical checks, recorded under evidence/.

Run from the repository root, on Linux (the comparator sandbox needs `bwrap`):

    python checks/lean_linux_run.py                # run and report
    python checks/lean_linux_run.py --record       # also write evidence/<date>-lean-linux/

Prerequisite, once: `cd lean && lake exe cache get` (prebuilt Mathlib, as the framework
requires). The run deletes lean/.lake/build twice, so that both the plain build and the
sandboxed comparator build start from nothing; Mathlib's cached build is kept.

Lake writes its exports to $TMPDIR. `lake check` exports everything the build imports, which
is all of Mathlib (about 6 GB); where /tmp is held in memory that does not fit, so the lake
steps get TMPDIR on disk (~/.cache/hubbard-lean-tmp, removed afterwards).

Every step has an expected exit code; the run passes only if all of them match. The sandbox
is never disabled here. A record from a dirty working tree is marked as such and is not the
final evidence.
"""
import hashlib
import json
import os
import platform
import re
import resource
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
CONTROLS = {   # config in lean/NegativeControls/ -> error lake comparator must give
    "weakened": "statement do not match: 'HubbardMoments.secondMomentTheorem'",
    "added-axiom": "Illegal axiom detected: 'HubbardMoments.secondMomentCheat'",
    "changed-definition": "Const does not match between challenge and target "
                          "'HubbardMoments.Spec.SecondMomentTheorem'",
    "sorry": "Illegal axiom detected: 'sorryAx'",
}


def sh(*cmd, cwd=ROOT):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True).stdout.strip()


def main_theorems():
    return re.findall(r"^theorem (\w+) : Spec\.\w+ :=", (LEAN / "HubbardMoments/Main.lean").read_text(), re.M)


def hygiene():
    """Every Lean file: SPDX line and a module docstring; no native evaluation anywhere."""
    issues = []
    files = sorted(p for p in LEAN.rglob("*.lean") if ".lake" not in p.parts)
    for p in files:
        text = p.read_text()
        rel = p.relative_to(LEAN)
        if not text.startswith("-- SPDX-License-Identifier:"):
            issues.append(f"{rel}: no SPDX line")
        if "/-!" not in text:
            issues.append(f"{rel}: no module docstring")
        if re.search(r"native_decide|decide \+native|bv_decide", text):
            issues.append(f"{rel}: native evaluation")
    return files, issues


def audit(log):
    """Parse `#print axioms`: every Main theorem appears once, with permitted axioms only."""
    found = {}
    for name, axioms in re.findall(r"'HubbardMoments\.(\w+)' depends on axioms: \[([^\]]*)\]", log):
        found[name] = {a.strip() for a in axioms.split(",") if a.strip()}
    for name in re.findall(r"'HubbardMoments\.(\w+)' does not depend on any axioms", log):
        found[name] = set()
    expected = set(main_theorems())
    bad = {n: sorted(a - PERMITTED) for n, a in found.items() if a - PERMITTED}
    return {"theorems": len(found), "expected": len(expected),
            "missing": sorted(expected - set(found)), "extra": sorted(set(found) - expected),
            "non_permitted": bad,
            "ok": set(found) == expected and not bad}


def main():
    record = "--record" in sys.argv[1:]
    t0 = time.time()
    date = time.strftime("%Y-%m-%d")
    out = ROOT / "evidence" / f"{date}-lean-linux"
    k = 2
    while out.exists():   # records are never overwritten: a second run that day gets -2, -3, ...
        out = ROOT / "evidence" / f"{date}-lean-linux-{k}"
        k += 1
    logs = {}
    steps = []

    tmp = Path.home() / ".cache" / "hubbard-lean-tmp"
    tmp.mkdir(parents=True, exist_ok=True)
    lake_env = dict(os.environ, TMPDIR=str(tmp))

    def run(name, cmd, expect, cwd=LEAN, must_contain=None):
        s = time.time()
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, env=lake_env)
        log = p.stdout + p.stderr
        logs[name] = log
        ok = p.returncode == expect and (must_contain is None or must_contain in log)
        step = {"step": name, "command": " ".join(cmd), "cwd": str(cwd.relative_to(ROOT)) or ".",
                "exit": p.returncode, "expected_exit": expect, "wall_time_s": round(time.time() - s, 1),
                "pass": ok}
        if must_contain:
            step["must_contain"] = must_contain
        steps.append(step)
        print(f"{'PASS' if ok else 'FAIL'}  {name:<34} exit {p.returncode} (expected {expect}), "
              f"{step['wall_time_s']} s", flush=True)
        return step, log

    files, issues = hygiene()
    steps.append({"step": "hygiene", "files": len(files), "issues": issues, "pass": not issues})
    print(f"{'PASS' if not issues else 'FAIL'}  {'hygiene':<34} {len(files)} files, {len(issues)} issue(s)")
    for i in issues:
        print("      ", i)

    shutil.rmtree(LEAN / ".lake" / "build", ignore_errors=True)
    st, log = run("clean build (lake build)", ["lake", "build"], 0)
    warnings = [line for line in log.splitlines() if line.startswith("warning:")]
    st["warnings"] = len(warnings)
    if warnings:
        st["pass"] = False
        print(f"FAIL  build warnings: {len(warnings)}")

    st, log = run("axiom audit", ["lake", "env", "lean", "AxiomAudit.lean"], 0)
    a = audit(log)
    st.update(audit=a)
    st["pass"] = st["pass"] and a["ok"]
    print(f"{'PASS' if a['ok'] else 'FAIL'}  {'  audit content':<34} {a['theorems']}/{a['expected']} "
          f"theorems, non-permitted: {a['non_permitted'] or 'none'}")

    shutil.rmtree(LEAN / ".lake" / "build", ignore_errors=True)
    run("lake comparator --paranoid", ["lake", "comparator", "--paranoid"], 0,
        must_contain="Your solution is okay!")
    for c, msg in CONTROLS.items():
        run(f"negative control: {c}", ["lake", "comparator", f"--config=NegativeControls/{c}.json"], 1,
            must_contain=msg)
    run("numerical checks", [sys.executable, "checks/run_checks.py"], 0, cwd=ROOT)
    run("lake check", ["lake", "check"], 0)   # all of Mathlib: last, and the slowest
    shutil.rmtree(tmp, ignore_errors=True)

    passed = all(s["pass"] for s in steps)
    print(f"\n{'ALL PASS' if passed else 'FAILED'}: {sum(s['pass'] for s in steps)}/{len(steps)} steps "
          f"in {time.time() - t0:.0f} s")
    if not record:
        return 0 if passed else 1

    git = lambda *a: sh("git", *a)  # noqa: E731
    osr = dict(line.split("=", 1) for line in Path("/etc/os-release").read_text().splitlines()
               if "=" in line) if Path("/etc/os-release").exists() else {}
    env = {"date": time.strftime("%Y-%m-%d %H:%M:%S %Z"), "machine": platform.machine(),
           "os": osr.get("PRETTY_NAME", platform.platform()).strip('"'), "kernel": platform.release(),
           "cpus": os.cpu_count(), "python": platform.python_version(),
           "numpy": __import__("numpy").__version__, "scipy": __import__("scipy").__version__,
           "lean": sh("lean", "--version", cwd=LEAN), "lake": sh("lake", "--version", cwd=LEAN),
           "elan": sh("elan", "--version"), "bwrap": sh("bwrap", "--version"),
           "lean_toolchain": (LEAN / "lean-toolchain").read_text().strip(),
           "mathlib_rev": re.search(r'rev = "(\w+)"', (LEAN / "lakefile.toml").read_text()).group(1),
           "git_commit": git("rev-parse", "HEAD"),
           "working_tree_dirty": git("status", "--porcelain", "--", ".", ":(exclude)evidence") != ""}
    result = {"passed": passed, "steps": steps, "wall_time_s": round(time.time() - t0, 1),
              "peak_rss_children_mb": round(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024, 1)}
    (out / "logs").mkdir(parents=True)
    for name, log in logs.items():
        (out / "logs" / (re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-") + ".log")).write_text(log)
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    (out / "environment.json").write_text(json.dumps(env, indent=2) + "\n")
    (out / "command.txt").write_text(" ".join([Path(sys.executable).name] + sys.argv) + "\n")
    files = sorted(p.relative_to(out).as_posix() for p in out.rglob("*") if p.is_file())
    (out / "SHA256SUMS").write_text("".join(
        f"{hashlib.sha256((out / f).read_bytes()).hexdigest()}  {f}\n" for f in files))
    print(f"recorded in {out.relative_to(ROOT)}"
          + ("  (WORKING TREE DIRTY: not final evidence)" if env["working_tree_dirty"] else ""))
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
