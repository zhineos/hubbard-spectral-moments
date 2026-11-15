"""Write a dated evidence record (docs/framework.md, section 5)."""
import hashlib
import json
import os
import platform
import resource
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def peak_rss_mb():
    r = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return round(r / 2 ** 20 if platform.system() == "Darwin" else r / 2 ** 10, 1)


def write_record(outdir, record, t0):
    out = Path(outdir)
    out.mkdir(parents=True, exist_ok=False)
    record = dict(record, wall_time_s=round(time.time() - t0, 1), peak_rss_mb=peak_rss_mb())
    git = lambda *a: subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True,  # noqa: E731
                                    text=True).stdout.strip()
    env = {"date": time.strftime("%Y-%m-%d %H:%M:%S %Z"), "machine": platform.machine(),
           "os": platform.platform(), "cpus": os.cpu_count(), "python": platform.python_version(),
           "numpy": __import__("numpy").__version__, "scipy": __import__("scipy").__version__,
           "git_commit": git("rev-parse", "HEAD"),
           # other evidence records (often untracked until committed) do not make the code dirty
           "working_tree_dirty": git("status", "--porcelain", "--", ".", ":(exclude)evidence") != ""}
    (out / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    (out / "environment.json").write_text(json.dumps(env, indent=2) + "\n")
    (out / "command.txt").write_text(" ".join([Path(sys.executable).name] + sys.argv) + "\n")
    (out / "SHA256SUMS").write_text("".join(
        f"{hashlib.sha256((out / f).read_bytes()).hexdigest()}  {f}\n"
        for f in ["command.txt", "environment.json", "result.json"]))
    return record
