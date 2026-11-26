"""Build and replay each research module and check the result declarations."""

from pathlib import Path
import subprocess

AUDIT = Path(__file__).with_name("Audit.lean").resolve()


def verify():
    root = Path("conjectures")
    sources = sorted(root.rglob("*.lean"))
    contracts = sorted(root.glob("*/axioms"))
    groups = {path.parent: [] for path in contracts}
    for path in sources:
        group = root / path.relative_to(root).parts[0]
        if group not in groups:
            raise SystemExit(f"Missing axiom contract for {path}")
        groups[group].append(".".join(path.with_suffix("").parts))

    subprocess.run(["lake", "build"], check=True)
    for group, modules in groups.items():
        if not modules:
            raise SystemExit(f"No Lean sources for {group}/axioms")
        # The replay report also detects a source omitted from the Lake targets.
        prefix = ".".join(group.parts)
        result = subprocess.run(
            ["lake", "env", "leanchecker", "--verbose", prefix],
            check=True, stdout=subprocess.PIPE, text=True,
        )
        replayed = {line.removeprefix("replaying ") for line in result.stdout.splitlines()
                    if line.startswith("replaying ")}
        if replayed != set(modules):
            raise SystemExit(f"Incomplete replay for {group}: {sorted(replayed ^ set(modules))}")
        print(f"Replayed {len(modules)} modules in {group}", flush=True)
        subprocess.run(["lake", "env", "lean", "--run", str(AUDIT),
                        str(group / "axioms"), *modules], check=True)


if __name__ == "__main__":
    verify()
