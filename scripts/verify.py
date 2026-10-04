#!/usr/bin/env python3
"""Check source coverage, then build every verification target (Python 3.9+)."""

import argparse
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
# The same list drives both the coverage audit and the actual build.
TARGETS = ("LTLLib", "LTLLibTests")
LAKE = ("lake", "--no-cache", "--no-ansi")


def query(targets):
    """Let Lake resolve globs, imports and source directories; do not parse Lean."""
    result = subprocess.run(
        [*LAKE, "-q", "query", "--json", *targets],
        cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True,
    )
    values = [json.loads(line) for line in result.stdout.splitlines()]
    if len(values) != len(targets):
        raise ValueError("Lake returned an unexpected number of query results")
    return values


def source_files():
    # Include existing tracked AND new, non-ignored files anywhere in the repo.
    # Dependency/build directories such as .lake are excluded by .gitignore.
    result = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True,
    )
    return {
        (ROOT / name).resolve()
        for name in result.stdout.split("\0")
        if name and (ROOT / name).is_file()
    }


def check_coverage():
    groups = query([f"{target}:modules" for target in TARGETS])
    selected = sorted({name for group in groups for name in group})
    if not selected:
        raise ValueError("Verification targets selected no modules")
    # A library's :modules facet includes only its own local import closure.
    # Follow cross-library imports too, including future local dependencies.
    imports = query([f"+{name}:transImports" for name in selected])
    closure = sorted(set(selected).union(name for group in imports for name in group))
    paths = query([f"+{name}:lean" for name in closure])
    covered = {Path(path).resolve() for path in paths}
    sources = source_files()
    missing = sorted(sources - covered)
    for target, group in zip(TARGETS, groups):
        print(f"{target}: {len(group)} selected modules (including local imports)", flush=True)
    print(f"Source coverage: {len(sources & covered)}/{len(sources)} Lean files", flush=True)
    if missing:
        print("Uncovered Lean sources; add a build target/glob or import:", file=sys.stderr)
        for path in missing:
            print(f"  {path.relative_to(ROOT)}", file=sys.stderr)
        return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coverage-only", action="store_true", help="audit sources without compiling")
    args = parser.parse_args()
    try:
        if not check_coverage():
            return 1
        if args.coverage_only:
            return 0
        command = [*LAKE, "build", *TARGETS]
        print("Running: " + " ".join(command), flush=True)
        # Inherit output and propagate Lean elaboration, #eval and axiom-guard failures.
        return subprocess.run(command, cwd=ROOT).returncode
    except subprocess.CalledProcessError as error:
        return error.returncode
    except (OSError, ValueError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
