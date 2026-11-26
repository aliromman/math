"""Build and replay each research module and check the result declarations."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import subprocess
import sys

AUDIT = Path(__file__).with_name("Audit.lean").resolve()


def research_groups():
    tracked = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"]).decode().split("\0")
    tools = {"scripts/Audit.lean", "scripts/Replay.lean", "scripts/ResearchLint.lean"}
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


def replay_source(source):
    artifact = Path(".lake/build/lib/lean") / source.with_suffix(".olean")
    if not artifact.is_file():
        raise SystemExit(f"Incomplete replay: missing {artifact}")
    module = ".".join(source.with_suffix("").parts)
    result = subprocess.run(["lean", str(AUDIT.with_name("Replay.lean"))],
                            env={**os.environ, "RESEARCH_REPLAY_MODULE": module})
    if result.returncode:
        raise SystemExit(f"Kernel replay failed for {module} (exit {result.returncode})")


def replay():
    groups = research_groups()
    sources = (source for files in groups.values() for source in files)
    with ThreadPoolExecutor(max_workers=2) as workers:
        list(workers.map(replay_source, sources))
    for group, sources in groups.items():
        subprocess.run(["lean", "--run", str(AUDIT), str(group / "axioms"),
                        *(str(source) for source in sources)], check=True)
        print(f"Replayed {len(sources)} modules in {group}", flush=True)


if __name__ == "__main__":
    if sys.argv[1:] == ["--replay"]:
        replay()
    elif not sys.argv[1:]:
        subprocess.run(["lake", "build"], check=True)
        subprocess.run(["lake", "env", sys.executable, str(Path(__file__).resolve()), "--replay"],
                       check=True)
    else:
        raise SystemExit("Usage: python3 scripts/verify.py")
