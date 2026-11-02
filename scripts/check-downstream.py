#!/usr/bin/env python3
"""Compile a separate Lake client, sharing the pinned dependency caches."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def check_classical_boundary(root):
    pending = ["CutQueryComplexity.Classical"]
    seen = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        source = root.joinpath(*module.split(".")).with_suffix(".lean")
        for line in source.read_text().splitlines():
            if not line.startswith("import "):
                continue
            for imported in line.split()[1:]:
                if imported.startswith(("QuantumQueryComplexity", "CutQueryComplexity.Quantum")):
                    raise SystemExit(f"Classical boundary violation: {module} imports {imported}")
                if imported.startswith("CutQueryComplexity."):
                    pending.append(imported)
    print(f"Classical import boundary checked ({len(seen)} local modules).")


def main():
    root = Path(__file__).resolve().parent.parent
    check_classical_boundary(root)
    environment = os.environ.copy()
    environment.pop("LEAN_PATH", None)
    environment.pop("LEAN_SRC_PATH", None)
    environment.setdefault("LEAN_NUM_THREADS", "1")
    environment["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    with tempfile.TemporaryDirectory(prefix="cut-query-downstream-") as directory:
        client = Path(directory)
        (client / "lakefile.toml").write_text(
            'name = "CutQueryDownstream"\n'
            'defaultTargets = ["Downstream", "Coverage"]\n\n'
            '[[require]]\nname = "CutQueryComplexity"\n'
            f'path = {json.dumps(str(root))}\n\n'
            '[[lean_lib]]\nname = "Downstream"\n\n'
            '[[lean_lib]]\nname = "Coverage"\n'
        )
        shutil.copy2(root / "lean-toolchain", client / "lean-toolchain")
        for name in ("Downstream", "Coverage"):
            shutil.copy2(root / f"tests/downstream/{name}.lean", client / f"{name}.lean")
        packages = client / ".lake/packages"
        packages.mkdir(parents=True)
        manifest = json.loads((root / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            cached = root / ".lake/packages" / package["name"]
            if cached.is_dir():
                (packages / package["name"]).symlink_to(cached.resolve(), target_is_directory=True)
        for command in (["lake", "update"], ["lake", "build"]):
            subprocess.run(command, cwd=client, env=environment, check=True)
    print("Separate downstream Lake client passed.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from None
