"""Verify an unmodified source release. This does not compile Lean or certify a license."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import sys


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def safe_relative(root, name):
    rel = PurePosixPath(name)
    if rel.is_absolute() or ".." in rel.parts or "\\" in name or ":" in name:
        raise ValueError("unsafe manifest path: " + name)
    path = root.joinpath(*rel.parts)
    if not path.resolve().is_relative_to(root.resolve()) or path.is_symlink():
        raise ValueError("path escapes release or is a symlink: " + name)
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assets-dir", type=Path, help="directory containing the named attached source ZIPs and paper PDF")
    parser.add_argument("--require-publishable", action="store_true", help="also reject unresolved release identity/license metadata")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "RELEASE_MANIFEST.json").read_text(encoding="utf-8"))
    errors = []
    for name, item in manifest["files"].items():
        path = safe_relative(root, name)
        if not path.is_file():
            errors.append("missing file: " + name)
        elif path.stat().st_size != item["bytes"] or digest(path) != item["sha256"]:
            errors.append("changed file: " + name)
    checked_assets = 0
    if args.assets_dir:
        for name, item in manifest["external_assets"].items():
            path = safe_relative(args.assets_dir, name)
            if not path.is_file():
                errors.append("missing release asset: " + name)
            elif path.stat().st_size != item["bytes"] or digest(path) != item["sha256"]:
                errors.append("changed release asset: " + name)
            checked_assets += 1
    integrity_passed = not errors
    if args.require_publishable:
        expected = set(manifest["files"]) | {"RELEASE_MANIFEST.json"}
        actual = {p.relative_to(root).as_posix() for p in root.rglob("*")
                  if p.is_file() and ".git" not in p.relative_to(root).parts}
        errors.extend("unlisted file in publication folder: " + p for p in sorted(actual - expected))
        errors.extend("unresolved publication field: " + item for item in manifest["publication"]["pending"])
    print(json.dumps({"integrity_passed": integrity_passed, "files_checked": len(manifest["files"]),
                      "external_assets_checked": checked_assets, "publication_metadata_complete": not manifest["publication"]["pending"],
                      "Lean_compiled": False, "errors": errors}, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print("Release verification failed: " + str(error), file=sys.stderr)
        sys.exit(1)
