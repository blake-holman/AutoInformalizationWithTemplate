#!/usr/bin/env python3
"""Extract proof data from a built Lean project without changing its sources."""
import argparse
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("files", type=Path, nargs="+")
    args = parser.parse_args()
    project = args.project.resolve()
    extractor = Path(__file__).resolve().parents[1] / "ExportInfos"
    toolchain = (extractor / "lean-toolchain").read_text().strip()
    if (project / "lean-toolchain").read_text().strip() != toolchain:
        parser.error(f"project must use {toolchain}")
    files = [(project / file).resolve() for file in args.files]
    for file in files:
        if not file.is_relative_to(project) or not file.is_file() or file.suffix != ".lean":
            parser.error(f"expected a Lean source inside the project: {file}")
    probe = 'import os,json; print(json.dumps({k:os.environ.get(k, "") for k in ["LEAN_PATH", "LEAN_SRC_PATH"]}))'
    paths = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", probe], cwd=project, text=True))
    env = os.environ.copy()
    for key, value in paths.items():
        resolved = [str((project / p).resolve()) for p in value.split(os.pathsep) if p]
        own = extractor / ".lake/build/lib/lean" if key == "LEAN_PATH" else extractor
        env[key] = os.pathsep.join([str(own), *resolved])
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    env["INFORMALIZATION_EXPORT_DIR"] = str(output)
    for file in files:
        subprocess.run(["lean", "--run", str(extractor / "DataExtraction.lean"),
                        str(file.relative_to(project))], cwd=project, env=env, check=True)
        print(f"Extracted {file.relative_to(project)} to {output}", flush=True)


if __name__ == "__main__":
    main()
