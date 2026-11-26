"""Run real positive and negative controls with the same verifier as CI."""

from pathlib import Path
import subprocess
import sys
import tempfile

VERIFY = Path(__file__).with_name("verify.py").resolve()


def main():
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        group = root / "conjectures" / "Control"
        group.mkdir(parents=True)
        (root / "lean-toolchain").write_bytes(Path("lean-toolchain").read_bytes())
        (root / "lakefile.toml").write_text(
            'name = "controls"\ndefaultTargets = ["conjectures"]\n'
            '[leanOptions]\nwarningAsError = true\n'
            '[[lean_lib]]\nname = "conjectures"\nglobs = ["conjectures.+"]\n'
        )
        source = group / "Result.lean"
        contract = group / "axioms"
        valid = "theorem controlResult : True := True.intro\n"

        def check(label, body, expected, error=None):
            source.write_text(body)
            contract.write_text(expected)
            run = subprocess.run([sys.executable, str(VERIFY)], cwd=root,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if (run.returncode == 0) != (error is None) or (error and error not in run.stdout):
                raise SystemExit(f"{label} failed its control:\n{run.stdout}")
            print(f"Passed control: {label}", flush=True)

        check("valid proof", valid, "controlResult\n")
        check("ill-typed proof", "theorem controlResult : False := True.intro\n",
              "controlResult\n", "Type mismatch")
        check("placeholder", "theorem controlResult : False := by sorry\n",
              "controlResult\n", "uses `sorry`")
        check("unused private axiom", valid + "private axiom unexplained : False\n",
              "controlResult\n", "forbidden axiom")
        check("wrong exact list", valid, "controlResult propext\n", "expected [propext]")
        check("missing result", valid, "otherResult\n", "missing local declaration")
        check("suppressed placeholder warning",
              "set_option warningAsError false\n" + valid + "private theorem gap : False := by sorry\n",
              "controlResult\n", "forbidden axiom")
        check("missing contract entries", valid, "", "empty axiom contract")
        check("statement only", "def openQuestion : Prop := False\n", "statement openQuestion\n")
        check("statement presented as proof", "def openQuestion : Prop := False\n",
              "openQuestion\n", "incorrect declaration kind")

        # Put an additional source outside the configured Lake glob.
        (root / "lakefile.toml").write_text(
            (root / "lakefile.toml").read_text().replace(
                'globs = ["conjectures.+"]', 'roots = ["conjectures.Control.Result"]'))
        (group / "Omitted.lean").write_text("theorem omitted : True := True.intro\n")
        check("a module omitted from the build", valid, "controlResult\n", "Incomplete replay")
        contract.unlink()
        failed = subprocess.run([sys.executable, str(VERIFY)], cwd=root, capture_output=True, text=True)
        if failed.returncode == 0 or "Missing axiom contract" not in failed.stderr:
            raise SystemExit("A source without an axiom contract escaped verification")
        print("Passed control: missing axiom contract")


if __name__ == "__main__":
    main()
