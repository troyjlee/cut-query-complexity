#!/usr/bin/env python3
"""Exercise audit rejection paths in isolated Lean files, including indirect axioms."""

import os
from pathlib import Path
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parent.parent
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "1")
    prefix = "import CutQueryComplexityChecks.AxiomAudit\n"
    cases = [
        ("allowed", "theorem allowed : True := True.intro\n#audit_cut_decl allowed\n", None),
        ("indirect_axiom", "axiom forbidden : False\ntheorem indirect : False := forbidden\n"
         "#audit_cut_decl indirect\n", "forbidden axiom(s) [forbidden]"),
        ("sorry", "theorem unfinished : False := by sorry\n#audit_cut_decl unfinished\n",
         "forbidden axiom(s) [sorryAx]"),
        ("missing_decl", "#audit_cut_decl NotADeclaration\n", "does not exist"),
        ("missing_module", "#audit_cut_axioms [NotAModule] pins []\n", "not in the environment"),
        ("missing_pin", "#audit_cut_axioms [] pins [NotAPin]\n", "does not exist"),
        ("outside_pin", "#audit_cut_axioms [] pins [True.intro]\n", "which is not audited"),
        ("duplicate_module", "#audit_cut_axioms [QuantumQueryComplexity.Test.AxiomSupport, "
         "QuantumQueryComplexity.Test.AxiomSupport] pins []\n", "listed more than once"),
        ("empty_module", "import CutQueryComplexity.Classical\n"
         "#audit_cut_axioms [CutQueryComplexity.Classical] pins []\n", "contributes no declaration"),
    ]
    with tempfile.TemporaryDirectory(prefix="axiom-audit-", dir=root / ".lake") as directory:
        for name, body, error in cases:
            path = Path(directory) / f"{name}.lean"
            path.write_text(prefix + body)
            result = subprocess.run(["lake", "env", "lean", "--trust=0", str(path)],
                                    cwd=root, env=env, capture_output=True, text=True)
            output = result.stdout + result.stderr
            if (error is None and result.returncode != 0) or (
                error is not None and (result.returncode == 0 or error not in output)
            ):
                raise SystemExit(f"Audit probe {name} failed:\n{output}")
            print(f"Audit probe {name} passed.", flush=True)
    print("Axiom-audit acceptance and rejection probes passed.")


if __name__ == "__main__":
    main()
