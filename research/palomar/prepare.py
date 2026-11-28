"""Prepare Palomar thin wrappers from one immutable research commit."""

import argparse
import json
from pathlib import Path
import subprocess
import tomllib


ROOT = Path(__file__).resolve().parents[2]
REPOSITORY = "https://github.com/aliromman/math"


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def write_json(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("revision", help="commit of the substantive proof repository")
    parser.add_argument("destination", type=Path, help="new directory for the submission project")
    args = parser.parse_args()
    revision = git("rev-parse", "--verify", "--end-of-options", args.revision + "^{commit}").decode().strip()
    output = args.destination
    entries = tomllib.loads(Path(__file__).with_name("entries.toml").read_text())["entry"]

    def source(path):
        return git("show", f"{revision}:{path}")

    output.mkdir(parents=True, exist_ok=False)
    for name in ("lean-toolchain", "LICENSE"):
        (output / name).write_bytes(source(name))
    (output / ".gitignore").write_text("/.lake/\n")
    (output / "lakefile.toml").write_text(
        'name = "palomar_math"\ndefaultTargets = ["Palomar"]\n\n'
        '[[require]]\nname = "math"\n' + f'git = "{REPOSITORY}"\nrev = "{revision}"\n\n'
        '[[lean_lib]]\nname = "Palomar"\nglobs = ["Palomar.+"]\n'
    )
    # Preserve all resolved dependency revisions, including Mathlib's transitive dependencies.
    lock = json.loads(source("lake-manifest.json"))
    for package in lock["packages"]:
        package["inherited"] = True
    lock["packages"].insert(0, {
        "url": REPOSITORY, "type": "git", "subDir": None, "scope": "", "rev": revision,
        "name": "math", "manifestFile": "lake-manifest.json", "inputRev": revision,
        "inherited": False, "configFile": "lakefile.toml",
    })
    lock["name"] = "palomar_math"
    write_json(output / "lake-manifest.json", lock)

    index = ["# Mathematical conjectures\n", f"The proof sources and research notes are pinned to [this commit]({REPOSITORY}/tree/{revision}).\n"]
    for entry in entries:
        group = entry["group"]
        package = output / "Palomar" / group
        package.mkdir(parents=True)
        prefix = f"conjectures/{group}"
        note = f"{REPOSITORY}/blob/{revision}/{prefix}/README.md"
        statement = source(prefix + "/Statement.lean").decode()
        target = f"{group}.{entry['theorem']}"
        contract = [line.split() for line in source(prefix + "/axioms").decode().splitlines()]
        [axioms] = [row[1:] for row in contract if row and row[0] == target]
        (package / "Challenge.lean").write_text(statement.rstrip() + f"\n\nnamespace {group}\n\n"
            + f"/-- {entry['description']} -/\npublic theorem {entry['theorem']} : {entry['type']} := by\n  sorry\n\nend {group}\n")
        (package / "Solution.lean").write_text(f"module\n\npublic import conjectures.{group}.Solution\n")
        write_json(package / "comparator.json", {
            "challenge_module": f"Palomar.{group}.Challenge", "solution_module": f"Palomar.{group}.Solution",
            "theorem_names": [target], "definition_names": [], "permitted_axioms": axioms, "enable_nanoda": True,
        })
        metadata = {
            "version": "v0.4",
            "project": {"name": entry["title"], "description": entry["description"], "authors": ["Ali Romman"],
                        "license": "Apache-2.0", "responsible_maintainers": ["Ali Romman"]},
            "repository": {"substantive_formalization": {"id": "aliromman/math", "revision": revision}},
            "classification": {"arxiv": entry["arxiv"], "msc2020": entry["msc"]},
            "sources": [{"title": entry["title"], "type": "original-proof", "relationship": "other", "location": note},
                       *[{**item, "relationship": "background"} for item in entry["sources"]]],
            "status": {"scope": entry["scope"], "sorry_count": 0, "sorry_in_definitions": 0, "axioms": axioms},
            "automation": {"methods": [{"method": "agent", "models": [], "framework": "OpenAI Codex",
                "tool_setup": "Mathematical reasoning, Lean 4, Mathlib, and exact checks as described in the research note.",
                "cost": {"wall_time": "See the research ledger for measured campaign totals.", "spend_usd": "not tracked", "hardware": "not tracked per result"},
                "prompting_notes": "Find a proof or counterexample, match its statement to the source, and verify it independently."}],
                "spend_usd": "not tracked", "notes": "Ali Romman maintains the collection. Codex developed the argument and formalization. The research record does not identify a model for each proof. The linked note credits prior work."},
            "fidelity": {"divergences": entry["fidelity"]},
            "review": {"status": "repository audit", "reviewers": [], "notes": entry["review"]},
            "alignment": {"namespace": group, "statements": [{"source": entry["locator"], "lean": target,
                "module": f"conjectures.{group}.Solution", "status": "proved", "note": entry["scope"]}]},
            "acknowledgements": "Lean, Mathlib, the problem's authors, and the sources credited in the research note.",
        }
        # JSON is a YAML 1.2 subset. The registry reads this file as formalization.yaml.
        write_json(package / "formalization.yaml", metadata)
        index.append(f"- [#{entry['pr']} — {entry['title']}]({note}) · [Comparator](Palomar/{group}/comparator.json)\n")
    (output / "README.md").write_text("\n".join(index))


if __name__ == "__main__":
    main()
