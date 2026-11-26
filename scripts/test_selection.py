"""Check affected verification on clean checkouts of small Git commits."""

from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def git(repo, *args):
    return subprocess.check_output(["git", "-c", "user.name=Verification control", "-c",
                                    "user.email=control@example.invalid", "-c", "commit.gpgSign=false",
                                    *args], cwd=repo, text=True).strip()


def main():
    with tempfile.TemporaryDirectory() as temporary:
        base = Path(temporary) / "base"
        base.mkdir()
        git(base, "init", "--quiet")
        shutil.copytree(ROOT / "scripts", base / "scripts", ignore=shutil.ignore_patterns("__pycache__"))
        shutil.copy(ROOT / "lean-toolchain", base)
        (base / "lakefile.toml").write_text(
            'name = "controls"\ndefaultTargets = ["conjectures"]\n[leanOptions]\nwarningAsError = true\n'
            '[[lean_lib]]\nname = "conjectures"\nglobs = ["conjectures.+"]\nplugins = ["ResearchLint:shared"]\n'
            '[[lean_lib]]\nname = "ResearchLint"\nsrcDir = "scripts"\n')
        anchor = "conjectures/Anchor/Result.lean"
        middle = "conjectures/Middle/Result.lean"
        spare = "conjectures/Spare/Result.lean"
        origin = "module\npublic theorem anchorResult : True := True.intro\n"
        direct = "module\npublic import\n  conjectures.Anchor.Result\npublic theorem middleResult : True := anchorResult\n"
        other = "module\n/-\nimport conjectures.Anchor.Result\n-/\npublic theorem spareResult : True := True.intro\n"
        files = {anchor: origin, middle: direct, spare: other,
                 "conjectures/Tip/Result.lean": "module\nimport conjectures.Middle.Result\n"
                                               "public theorem tipResult : True := middleResult\n",
                 "conjectures/Spare/Keep.lean": "module\npublic theorem spareKeep : True := True.intro\n"}
        for group in ["Anchor", "Middle", "Tip", "Spare"]:
            files[f"conjectures/{group}/axioms"] = f"{group.lower()}Result\n"
        for path, content in files.items():
            dest = base / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(content)
        git(base, "add", ".")
        git(base, "commit", "--quiet", "-m", "Set up the import graph")
        previous = git(base, "rev-parse", "HEAD")

        def check(label, edits, expected=None, error=None, unbuilt=(), mode="affected"):
            with tempfile.TemporaryDirectory(dir=temporary) as checkout:
                repo = Path(checkout)
                git(repo, "clone", "--quiet", "--local", str(base), ".")
                for path, content in edits.items():
                    dest = repo / path
                    if content is None:
                        dest.unlink()
                    else:
                        dest.write_text(content)
                git(repo, "add", "-A")
                git(repo, "commit", "--quiet", "-m", label)
                head = git(repo, "rev-parse", "HEAD")
                git(repo, "checkout", "--quiet", "--detach", previous)
                git(repo, "merge", "--quiet", "--no-ff", "--no-edit", head)
                verify = [sys.executable, "scripts/verify.py", "--base", previous]
                selected = subprocess.check_output([*verify, "--mode"], cwd=repo, text=True).strip()
                if selected != mode:
                    raise SystemExit(f"{label} selected {selected}. Expected {mode}.")
                result = subprocess.run(verify,
                                        cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                groups = {g: int(n) for n, g in re.findall(
                    r"^Replayed (\d+) modules in conjectures/(\w+)$", result.stdout, re.MULTILINE)}
                objects = repo / ".lake/build/lib/lean/conjectures"
                if error:
                    passed = result.returncode != 0 and error in result.stdout
                else:
                    passed = result.returncode == 0 and groups == expected
                    passed = passed and all(not any((objects / group).glob("*.olean")) for group in unbuilt)
                if not passed:
                    raise SystemExit(f"{label} failed its control. Replayed {groups}.\n{result.stdout}")
                print(f"Passed selection control: {label}", flush=True)

        chain = {"Anchor": 1, "Middle": 1, "Tip": 1}
        all_groups = {**chain, "Spare": 2}
        check("direct and transitive imports", {anchor: origin.replace("True.intro", "by trivial")},
              chain, unbuilt=["Spare"])
        weakened = origin.replace(": True := True.intro", ": True ∨ False := Or.inl True.intro")
        check("changed premise invalidates importer", {anchor: weakened}, error="Type mismatch")
        check("unrelated source", {spare: other.replace("True.intro", "by trivial")},
              {"Spare": 1}, unbuilt=chain)
        check("documentation", {"README.md": "Fixture notes.\n", "conjectures/Spare/README.md": "Proof notes.\n"},
              {}, unbuilt=all_groups, mode="docs")
        check("changed contract", {"conjectures/Spare/axioms": "spareResult\nspareKeep\n"},
              {"Spare": 0}, unbuilt=chain)
        check("wrong changed contract", {"conjectures/Spare/axioms": "spareResult propext\n"},
              error="expected [propext]")
        moved = {anchor: None, "conjectures/Anchor/Renamed.lean": origin}
        check("renamed source and corrected import", {**moved, middle: direct.replace(".Result", ".Renamed")},
              chain, unbuilt=["Spare"])
        check("unchanged importer of renamed module", moved, error="imports missing research module conjectures.Anchor.Result")
        check("deleted contracted module", {spare: None}, error="missing local declaration spareResult")
        check("deleted contract", {"conjectures/Spare/axioms": None}, error="Missing axiom contract")
        for path in ["lean-toolchain", "scripts/verify.py"]:
            check(f"global change to {path}", {path: (base / path).read_text() + "\n"}, all_groups, mode="full")
        check("removed independent directory",
              {spare: None, "conjectures/Spare/Keep.lean": None, "conjectures/Spare/axioms": None},
              {}, unbuilt=all_groups, mode="affected")

        resource = "conjectures/Spare/README.md"
        (base / resource).write_text("first\n")
        (base / spare).write_text('module\npublic def note : String := include_str "README.md"\n'
                                  'public theorem spareResult : note = "first\\n" := rfl\n')
        git(base, "add", ".")
        git(base, "commit", "--quiet", "-m", "Read a proof input from Markdown")
        previous = git(base, "rev-parse", "HEAD")
        check("Markdown used by a proof", {resource: "second\n"}, error="rfl", mode="affected")


if __name__ == "__main__":
    main()
