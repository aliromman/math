"""Run real positive and negative controls with the same verifier as CI."""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

VERIFY = Path(__file__).with_name("verify.py").resolve()


def main():
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        subprocess.run(["git", "init", "--quiet", str(root)], check=True)
        group = root / "conjectures" / "Control"
        group.mkdir(parents=True)
        (root / "lean-toolchain").write_bytes(Path("lean-toolchain").read_bytes())
        shutil.copy(VERIFY.with_name("ResearchLint.lean"), root)
        (root / "lakefile.toml").write_text(
            'name = "controls"\ndefaultTargets = ["conjectures"]\n'
            '[leanOptions]\nwarningAsError = true\n'
            '[[lean_lib]]\nname = "conjectures"\nglobs = ["conjectures.+"]\n'
            'plugins = ["ResearchLint:shared"]\n[[lean_lib]]\nname = "ResearchLint"\n'
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
            return run.stdout

        check("valid proof", valid, "controlResult\n")
        check("guarded diagnostics", valid
              + "/-- info: 'controlResult' does not depend on any axioms -/\n"
              + "#guard_msgs in\n#print axioms controlResult\n"
              + "#guard_msgs (drop error) in\n#check unknownDiagnosticName\n",
              "controlResult\n")
        check("guarded theorem with visible errors",
              valid + "#guard_msgs (warning) in\ntheorem guardedResult : True := True.intro\n",
              "controlResult\nguardedResult\n")
        check("guarded invalid declaration",
              valid + "#guard_msgs (drop all) in\ntheorem discarded : MissingType := True.intro\n",
              "controlResult\n", "Pass errors from guarded declarations")
        check("safe recursion", valid + "def lengthOf : List Nat → Nat\n"
              + "  | [] => 0\n  | _ :: xs => lengthOf xs + 1\n", "controlResult\n")
        check("partial definition", valid + "partial def loop (n : Nat) : Nat := loop n\n",
              "controlResult\n", "kernel replay skips")
        check("unsafe definition", valid + "unsafe def rawValue : Nat := 0\n",
              "controlResult\n", "kernel replay skips")
        check("ill-typed proof", "theorem controlResult : False := True.intro\n",
              "controlResult\n", "Type mismatch")
        check("placeholder", "theorem controlResult : False := by sorry\n",
              "controlResult\n", "uses `sorry`")
        # Construct a malformed proof with Lean's documented kernel debug option.
        kernel_log = check("kernel rejects an ill-typed object file",
              "import Lean\nopen Lean Elab Command\nset_option debug.skipKernelTC true in\n"
              + "run_cmd liftCoreM <| addDecl <| .thmDecl { name := `controlResult, "
              + "levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n",
              "controlResult\n", "(kernel) declaration type mismatch")
        if "Build completed successfully" not in kernel_log or "Replay.lean:" not in kernel_log:
            raise SystemExit("The kernel control must build before independent replay rejects it")
        check("unused private axiom", valid + "private axiom unexplained : False\n",
              "controlResult\n", "forbidden axiom")
        check("wrong exact list", valid, "controlResult propext\n", "expected [propext]")
        check("missing result", valid, "otherResult\n", "missing local declaration")
        check("suppressed placeholder warning",
              "set_option warningAsError false\n" + valid + "private theorem gap : False := sorryAx False false\n",
              "controlResult\n", "forbidden axiom")
        check("discarded anonymous example", valid + "set_option warn.sorry false\n"
              + "example : False := by sorry\n", "controlResult\n", "Give the example a theorem name")
        check("discarded proof inside a message guard",
              valid + "#guard_msgs (drop all) in\nexample : False := by sorry\n",
              "controlResult\n", "Give the example a theorem name")
        check("placeholder inside a diagnostic term",
              valid + "#guard_msgs (drop all) in\n#check (by admit : False)\n",
              "controlResult\n", "Replace the proof placeholder")
        check("early exit", valid + "set_option warningAsError false\n#exit\n",
              "controlResult\n", "complete research module")
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
        (root / "Other.lean").write_text(valid)
        subprocess.run(["git", "add", "Other.lean"], cwd=root, check=True)
        failed = subprocess.run([sys.executable, str(VERIFY)], cwd=root, capture_output=True, text=True)
        if failed.returncode == 0 or "outside the verified library" not in failed.stderr:
            raise SystemExit("An extra tracked Lean source escaped verification")
        print("Passed control: proof outside the verified library")


if __name__ == "__main__":
    main()
