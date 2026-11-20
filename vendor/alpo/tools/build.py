#!/usr/bin/env python3
"""Build the vendored alpo.ge Lean tree with a hard cap on concurrency.

Why not `lake build`: Lake v4.33 has no -j option.  On 2026-11-20 an unthrottled
`lake build Main` of this 175k-module tree exhausted the system-wide file table
("Too many open files in system") and the host kernel panicked.  This script compiles the
tree's own modules itself, in dependency order, with

  * at most --jobs `lean` processes at a time (default: half the CPUs), each single-threaded
    (`lean -j1`) and under `nice`;
  * a watchdog that kills every child and stops when the system file table passes
    --max-file-frac of its limit or free memory drops below --min-free-mem-frac;
  * the same Lean options Lake would pass (read from the tree's lakefile.toml);
  * resumability: a module whose .olean is newer than its source and than the .oleans of its
    imports is skipped, and every .olean is written to a temporary name and renamed, so an
    interrupted run never leaves a truncated file behind.

Mathlib is not compiled here: run `lake exe cache get` in the tree first.

Usage:
    python3 -I vendor/alpo/tools/build.py --root vendor/alpo/lean [--jobs N] [--target Main]
    python3 -I vendor/alpo/tools/build.py --root vendor/alpo/lean --dry-run
"""
import argparse
import heapq
import json
import os
import re
import signal
import subprocess
import sys
import time

try:
    import tomllib
except ModuleNotFoundError:
    sys.exit("build.py needs Python 3.11 or later (tomllib)")

TOKEN = re.compile(r"\S+")


def read_imports(path):
    """The modules imported by a Lean file (header only; comments are skipped)."""
    imports, depth = [], 0
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            text, i, out = line, 0, []
            while i < len(text):
                if depth:
                    if text.startswith("/-", i):
                        depth, i = depth + 1, i + 2
                    elif text.startswith("-/", i):
                        depth, i = depth - 1, i + 2
                    else:
                        i += 1
                elif text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("--", i):
                    break
                else:
                    out.append(text[i])
                    i += 1
            tokens = TOKEN.findall("".join(out))
            if not tokens:
                continue
            if tokens[0] != "import":
                return imports
            imports.extend(t for t in tokens[1:] if t != "import")
    return imports


def lean_options(lakefile):
    """(global -D options, extra args, [(module prefix, -D options)]) from lakefile.toml."""
    with open(lakefile, "rb") as fh:
        cfg = tomllib.load(fh)

    def defs(opts):
        return [f"-D{k}={str(v).lower() if isinstance(v, bool) else v}" for k, v in opts.items()]

    def flatten(d, prefix=""):
        out = {}
        for k, v in d.items():
            if isinstance(v, dict):
                out.update(flatten(v, f"{prefix}{k}."))
            else:
                out[f"{prefix}{k}"] = v
        return out

    glob_opts = defs(flatten(cfg.get("leanOptions", {})))
    extra = list(cfg.get("moreLeanArgs", []))
    per_lib = []
    for lib in cfg.get("lean_lib", []):
        if "leanOptions" not in lib:
            continue
        opts = defs(flatten(lib["leanOptions"]))
        for g in lib.get("globs", []):
            if not g.endswith(".+"):
                sys.exit(f"unsupported glob {g!r} with lib-specific options")
            per_lib.append((g[:-2] + ".", opts))
    return glob_opts, extra, per_lib


def sysctl(name):
    return int(subprocess.run(["sysctl", "-n", name], capture_output=True, text=True).stdout)


def pressure():
    """(fraction of the system file table in use, fraction of memory free)."""
    if sys.platform == "darwin":
        files = sysctl("kern.num_files") / sysctl("kern.maxfiles")
        free = sysctl("kern.memorystatus_level") / 100
        return files, free
    with open("/proc/sys/fs/file-nr") as fh:
        used, _, limit = (int(x) for x in fh.read().split())
    mem = {}
    with open("/proc/meminfo") as fh:
        for line in fh:
            k, v = line.split(":")
            mem[k] = int(v.split()[0])
    return used / limit, mem["MemAvailable"] / mem["MemTotal"]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", required=True, help="the Lake package (contains lakefile.toml)")
    ap.add_argument("--target", nargs="+", default=["Main"])
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--max-file-frac", type=float, default=0.30)
    ap.add_argument("--min-free-mem-frac", type=float, default=0.15)
    ap.add_argument("--nice", type=int, default=10)
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    root = os.path.abspath(a.root)
    src = os.path.join(root, "src")
    out_dir = os.path.join(root, ".lake", "build", "lib", "lean")
    log_dir = os.path.join(root, ".lake", "alpo-build-logs")
    os.makedirs(log_dir, exist_ok=True)
    glob_opts, extra, per_lib = lean_options(os.path.join(root, "lakefile.toml"))
    toolchain = open(os.path.join(root, "lean-toolchain")).read().strip()

    # The import graph of the targets' closure.
    def src_of(m):
        return os.path.join(src, *m.split(".")) + ".lean"

    deps, stack = {}, list(a.target)
    while stack:
        m = stack.pop()
        if m in deps:
            continue
        p = src_of(m)
        if not os.path.isfile(p):
            if m in a.target:
                sys.exit(f"target {m} not found at {p}")
            continue
        deps[m] = [i for i in read_imports(p) if os.path.isfile(src_of(i))]
        stack.extend(deps[m])
    dependents = {m: [] for m in deps}
    for m, ds in deps.items():
        for d in ds:
            dependents[d].append(m)

    # Priority: longest chain of dependents above a module (critical path first).
    height, order, seen = {}, [], set()
    for m in deps:
        if m in seen:
            continue
        st = [(m, iter(deps[m]))]
        seen.add(m)
        while st:
            cur, it = st[-1]
            nxt = next((d for d in it if d not in seen), None)
            if nxt is None:
                st.pop()
                order.append(cur)
            else:
                seen.add(nxt)
                st.append((nxt, iter(deps[nxt])))
    for m in reversed(order):  # dependents before dependencies
        height[m] = 1 + max((height[d] for d in dependents[m]), default=0)

    def olean(m):
        return os.path.join(out_dir, *m.split(".")) + ".olean"

    def mtime(p):
        try:
            return os.stat(p).st_mtime_ns
        except FileNotFoundError:
            return None

    total = len(deps)
    up_to_date = set()
    for m in order:  # dependencies first
        t = mtime(olean(m))
        if t is not None and t >= mtime(src_of(m)) and all(
            d in up_to_date and mtime(olean(d)) <= t for d in deps[m]
        ):
            up_to_date.add(m)
    print(f"[build] {toolchain}; {total} modules in closure of {a.target}; "
          f"{len(up_to_date)} up to date; {total - len(up_to_date)} to build; jobs={a.jobs}",
          flush=True)
    if a.dry_run:
        return 0

    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=root,
                               capture_output=True, text=True, check=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=lean_path)

    pending = {m: sum(1 for d in deps[m] if d not in up_to_date) for m in deps if m not in up_to_date}
    ready = [(-height[m], m) for m, n in pending.items() if n == 0]
    heapq.heapify(ready)
    running = {}  # pid -> (module, Popen, tmp olean, tmp ilean, log path, start)
    done, failed, blocked = set(up_to_date), [], 0
    t0, last_report = time.time(), 0.0

    def kill_all(reason):
        for _, p, *_ in running.values():
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        for _, p, o, i, *_ in running.values():
            p.wait()
            for f in (o, i):
                if os.path.exists(f):
                    os.remove(f)
        print(f"[build] STOPPED: {reason}", flush=True)

    def on_signal(signum, _frame):
        kill_all(f"signal {signum}")
        sys.exit(130)

    signal.signal(signal.SIGINT, on_signal)
    signal.signal(signal.SIGTERM, on_signal)

    while ready or running:
        while ready and len(running) < a.jobs:
            _, m = heapq.heappop(ready)
            o = olean(m)
            os.makedirs(os.path.dirname(o), exist_ok=True)
            tmp_o, tmp_i = o + ".tmp", o[: -len(".olean")] + ".ilean.tmp"
            opts = list(glob_opts)
            for prefix, lib_opts in per_lib:
                if m.startswith(prefix):
                    opts += lib_opts
            log = os.path.join(log_dir, m + ".log")
            cmd = ["nice", "-n", str(a.nice), "lean", "-j1", *extra, *opts, src_of(m),
                   "-o", tmp_o, "-i", tmp_i]
            fh = open(log, "w")
            p = subprocess.Popen(cmd, cwd=root, env=env, stdout=fh, stderr=subprocess.STDOUT,
                                 start_new_session=True)
            fh.close()
            running[p.pid] = (m, p, tmp_o, tmp_i, log, time.time())

        files, free = pressure()
        if files > a.max_file_frac or free < a.min_free_mem_frac:
            kill_all(f"watchdog: file table {files:.0%} used, memory {free:.0%} free")
            return 3

        for pid, (m, p, tmp_o, tmp_i, log, start) in list(running.items()):
            if p.poll() is None:
                continue
            del running[pid]
            if p.returncode == 0:
                os.replace(tmp_i, olean(m)[: -len(".olean")] + ".ilean")
                os.replace(tmp_o, olean(m))
                os.remove(log)
                done.add(m)
                for d in dependents[m]:
                    if d in pending:
                        pending[d] -= 1
                        if pending[d] == 0:
                            heapq.heappush(ready, (-height[d], d))
            else:
                failed.append(m)
                print(f"[build] FAILED {m} (exit {p.returncode}); log: {log}", flush=True)

        now = time.time()
        if now - last_report > 60:
            built = len(done) - len(up_to_date)
            rate = built / max(now - t0, 1)
            left = total - len(done)
            eta = left / rate / 3600 if rate else float("inf")
            print(f"[build] {len(done)}/{total} done ({built} built this run, {rate * 60:.1f}/min), "
                  f"{len(running)} running, {len(failed)} failed, ETA {eta:.1f} h; "
                  f"file table {files:.1%}, memory free {free:.0%}", flush=True)
            last_report = now
        time.sleep(0.5)

    blocked = total - len(done) - len(failed)
    summary = {"toolchain": toolchain, "targets": a.target, "modules": total, "done": len(done),
               "failed": failed, "blocked_by_failures": blocked,
               "hours": round((time.time() - t0) / 3600, 2)}
    with open(os.path.join(log_dir, "summary.json"), "w") as fh:
        json.dump(summary, fh, indent=1)
    print(f"[build] finished: {json.dumps(summary)}", flush=True)
    return 0 if not failed and blocked == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
