"""Build and replay each research module and check the result declarations."""

import argparse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import os
import re
import subprocess
import sys

AUDIT = Path(__file__).with_name("Audit.lean").resolve()


def research_groups():
    tracked = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"]).decode().split("\0")
    tools = {"scripts/Audit.lean", "scripts/ResearchLint.lean"}
    for path in filter(None, tracked):
        if not path.startswith("conjectures/") and path not in tools:
            raise SystemExit(f"Lean source outside the verified library: {path}")

    root = Path("conjectures")
    groups = {path.parent: [] for path in sorted(root.glob("*/axioms"))}
    for path in sorted(root.rglob("*.lean")):
        group = root / path.relative_to(root).parts[0]
        if group not in groups:
            raise SystemExit(f"Missing axiom contract for {path}")
        groups[group].append(path)
    for group, sources in groups.items():
        if not sources:
            raise SystemExit(f"No Lean sources for {group}/axioms")
    return groups



def verification_inputs(base):
    """Return changed project inputs. None requests a full audit."""
    if not base:
        return None
    names = subprocess.check_output(["git", "diff", "--no-renames", "--name-only", "-z",
                                     base, "HEAD", "--"]).decode().split("\0")
    changed = set()
    auxiliary = set()
    for name in filter(None, names):
        path = Path(name)
        if path.suffix == ".md" or name in {"CITATION.cff", "LICENSE", "NOTICE", ".mailmap"}:
            auxiliary.add(path.name)
            continue
        if path.parts[0] != "conjectures" or len(path.parts) < 3:
            return None
        if path.suffix != ".svg":
            changed.add(path)
        if path.suffix != ".lean" and path.name != "axioms":
            auxiliary.add(path.name)
    if changed or auxiliary:
        # Import headers do not record external files that elaborators read.
        readers = re.compile(r"\b(include_str|include_bytes|bv_check|readFile|readBinFile|withFile|IO\.FS)\b")
        for source in Path("conjectures").rglob("*.lean"):
            if source.is_symlink():
                changed.add(source)
                continue
            text = source.read_text()
            if readers.search(text) or any(name in text for name in auxiliary):
                changed.add(source)
    return changed


def module_name(path):
    return ".".join(path.with_suffix("").parts)


def import_graph(sources):
    if not sources:
        return {}
    rows = json.loads(subprocess.check_output(["lean", "--deps-json", *map(str, sources)]))["imports"]
    if len(rows) != len(sources):
        raise SystemExit("Incomplete Lean import inventory")
    graph = {}
    for path, row in zip(sources, rows):
        if row["errors"] or not row.get("result"):
            raise SystemExit(f"Cannot read the imports of {path}: {row['errors']}")
        module = module_name(path)
        if module in graph:
            raise SystemExit(f"More than one file defines research module {module}")
        graph[module] = {item["module"] for item in row["result"]["imports"]}
    for module, imports in graph.items():
        for imported in imports:
            if imported.startswith("conjectures.") and imported not in graph:
                raise SystemExit(f"{module} imports missing research module {imported}")
    return graph


def closure(seeds, edges):
    result = set(seeds)
    pending = list(result)
    while pending:
        for name in edges.get(pending.pop(), ()):
            if name not in result:
                result.add(name)
                pending.append(name)
    return result


def affected(groups, changed, imports):
    if changed is None:
        return groups, set(imports)
    reverse = defaultdict(set)
    for module, dependencies in imports.items():
        for dependency in dependencies:
            reverse[dependency].add(module)
    owners = {Path(*path.parts[:2]) for path in changed}
    seeds = {module_name(path) for path in changed if path.suffix == ".lean"}
    for path in changed:
        if path.suffix != ".lean" and path.name != "axioms":
            seeds.update(module_name(p) for p in groups.get(Path(*path.parts[:2]), ()))
    replay = closure(seeds, reverse)
    for group, sources in groups.items():
        if any(module_name(p) in replay for p in sources):
            owners.add(group)
    return {g: sources for g, sources in groups.items() if g in owners}, replay

def replay_group(job):
    group, sources, selected = job
    expected = {module_name(source) for source in sources if module_name(source) in selected}
    if not expected:
        return
    for module in sorted(expected):
        artifact = Path(".lake/build/lib/lean", *module.split(".")).with_suffix(".olean")
        if not artifact.is_file():
            raise SystemExit(f"Incomplete replay: missing {artifact}")
    # The release CLI accepts module prefixes. A full group needs only one object-file scan.
    targets = [".".join(group.parts)] if len(expected) == len(sources) else sorted(expected)
    result = subprocess.run(["leanchecker", "--verbose", *targets], stdout=subprocess.PIPE,
                            text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
    if result.returncode:
        raise SystemExit(f"Kernel replay failed for {', '.join(targets)} (exit {result.returncode})")
    checked = {line.removeprefix("replaying ") for line in result.stdout.splitlines() if line.startswith("replaying ")}
    if missing := expected - checked:
        raise SystemExit(f"Incomplete replay: {', '.join(sorted(missing))}")



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", help="compare this Git commit with HEAD")
    parser.add_argument("--mode", action="store_true", help="print docs, affected, or full")
    parser.add_argument("--fetch-cache", action="store_true", help="fetch the required Mathlib objects")
    parser.add_argument("--replay", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    changed = verification_inputs(args.base)
    mode = "full" if changed is None else "affected" if changed else "docs"
    if args.mode:
        print(mode)
        return
    if mode == "docs":
        print("No proof verification inputs changed.")
        return

    groups = research_groups()
    imports = import_graph([p for sources in groups.values() for p in sources])
    groups, selected = affected(groups, changed, imports)
    build = [module_name(p) for sources in groups.values() for p in sources]
    if not args.replay:
        for path in sorted(p for p in changed or () if not p.exists()):
            print(f"Removed verification input: {path}", flush=True)
        if args.fetch_cache:
            dependencies = closure(build, imports)
            mathlib = sorted(n for n in dependencies if n == "Mathlib" or n.startswith("Mathlib."))
            if mathlib:
                subprocess.run(["lake", "exe", "cache", "get", *mathlib], check=True)
        if mode == "full" or build:
            # Independent Lake targets can otherwise build the same shared plugin concurrently.
            subprocess.run(["lake", "build", "ResearchLint:shared"], check=True)
        if mode == "full":
            subprocess.run(["lake", "build"], check=True)
        elif build:
            subprocess.run(["lake", "build", *(f"+{name}:olean" for name in build)], check=True)
        cmd = ["lake", "env", sys.executable, str(Path(__file__).resolve()), "--replay"]
        subprocess.run(cmd + (["--base", args.base] if args.base else []), check=True)
        return

    sources = [p for files in groups.values() for p in files if module_name(p) in selected]
    with ThreadPoolExecutor(max_workers=2) as workers:
        list(workers.map(replay_group, ((g, paths, selected) for g, paths in groups.items())))
    for group, files in groups.items():
        subprocess.run(["lean", "--run", str(AUDIT), str(group / "axioms"), *map(str, files)], check=True)
        count = sum(module_name(p) in selected for p in files)
        print(f"Replayed {count} modules in {group}", flush=True)
    print(f"Verified {len(sources)} research modules and {len(groups)} axiom contracts ({mode}).")


if __name__ == "__main__":
    main()
