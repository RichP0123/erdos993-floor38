#!/usr/bin/env python3
"""Configure this core against existing local packages; never run Git/Lake/downloads.

Lock and optional checkout-HEAD checks are metadata checks, not source/cache audits.
The only subprocess is an explicitly found direct Lean executable's --version.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib

TOOLCHAIN = "leanprover/lean4:v4.30.0"
LEAN_COMMIT = "d024af099ca4bf2c86f649261ebf59565dc8c622"
MATHLIB_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
ROOT = Path(__file__).resolve().parent


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(value, dict):
        raise ValueError(f"Expected a JSON object: {path}")
    return value


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def package_map(data: dict) -> dict[str, dict]:
    result = {}
    for package in data["packages"]:
        name = package["name"]
        if not re.fullmatch(r"[A-Za-z0-9_-]+", name) or name in result:
            raise ValueError(f"Invalid/duplicate package name: {name!r}")
        if package.get("type") != "git" or not re.fullmatch(
            r"[0-9a-f]{40}", package.get("rev", "")
        ):
            raise ValueError(f"A fixed Git revision is required in lock metadata: {name}")
        if package.get("subDir"):
            raise ValueError(f"Subdirectory packages are not supported: {name}")
        result[name] = package
    return result


def contained_ref(base: Path, ref: str) -> Path:
    if not ref.startswith("refs/"):
        raise ValueError(f"Invalid local Git ref: {ref!r}")
    path = (base / ref).resolve()
    if not path.is_relative_to(base.resolve()):
        raise ValueError("Ref escapes local Git metadata directory")
    return path


def local_head(checkout: Path) -> str | None:
    """Read small local Git metadata only, including worktree/packed refs."""
    marker = checkout / ".git"
    if not marker.exists():
        return None
    if marker.is_dir():
        git_dir = marker.resolve()
    else:
        line = marker.read_text(encoding="utf-8").strip()
        if not line.startswith("gitdir: "):
            raise ValueError(f"Unrecognized Git metadata file: {marker}")
        git_dir = (checkout / line[len("gitdir: "):]).resolve()
    common_file = git_dir / "commondir"
    common_dir = (git_dir / common_file.read_text(encoding="utf-8").strip()).resolve() \
        if common_file.is_file() else git_dir
    head = (git_dir / "HEAD").read_text(encoding="utf-8").strip()
    for _ in range(8):
        if re.fullmatch(r"[0-9a-fA-F]{40}", head):
            return head.lower()
        if not head.startswith("ref: "):
            raise ValueError(f"Cannot resolve local HEAD metadata: {checkout}")
        ref = head[5:]
        found = None
        for base in dict.fromkeys((git_dir, common_dir)):
            loose = contained_ref(base, ref)
            if loose.is_file():
                found = loose.read_text(encoding="utf-8").strip()
                break
            packed = base / "packed-refs"
            if packed.is_file():
                with packed.open(encoding="utf-8") as stream:
                    for line in stream:
                        parts = line.strip().split()
                        if len(parts) == 2 and parts[1] == ref:
                            found = parts[0]
                            break
            if found is not None:
                break
        if found is None:
            raise ValueError(f"Unresolved local HEAD reference: {checkout}: {ref}")
        head = found
    raise ValueError(f"Too many symbolic HEAD references: {checkout}")


def configured_path(path: Path) -> str:
    try:
        return Path(os.path.relpath(path, ROOT)).as_posix()
    except ValueError:  # Different Windows drives cannot have a relative path.
        return path.as_posix()


def direct_lean(requested: Path | None) -> Path | None:
    elan_home = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
    if requested is not None:
        candidate = requested.expanduser().resolve()
        if not candidate.is_file():
            raise ValueError(f"Direct Lean executable not found: {candidate}")
        if candidate.parent == (elan_home / "bin").resolve() or any(
            (candidate.parent / name).is_file() for name in ("elan", "elan.exe")
        ):
            raise ValueError("--lean points into an Elan launcher directory; use the installed toolchain binary")
        return candidate
    toolchain_bin = elan_home / "toolchains" / "leanprover--lean4---v4.30.0" / "bin"
    for filename in ("lean.exe", "lean"):
        candidate = toolchain_bin / filename
        if candidate.is_file():
            return candidate.resolve()
    return None


def atomic_write(path: Path, text: str) -> None:
    descriptor, temporary = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(text)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def configure(args: argparse.Namespace) -> dict:
    expected_toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    if expected_toolchain != TOOLCHAIN:
        raise ValueError("Core lean-toolchain does not match the required pinned toolchain")
    lock_path = ROOT / "UPSTREAM_LOCK.json"
    locked = package_map(read_json(lock_path))
    if locked.get("mathlib", {}).get("rev") != MATHLIB_COMMIT:
        raise ValueError("UPSTREAM_LOCK.json does not pin the expected Mathlib commit")

    mathlib = args.mathlib.expanduser().resolve()
    if not mathlib.is_dir():
        raise ValueError(f"Mathlib checkout directory missing: {mathlib}")
    if mathlib.is_relative_to(ROOT):
        raise ValueError("Use an existing Mathlib checkout outside this core directory")
    mathlib_toolchain = (mathlib / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    if mathlib_toolchain != TOOLCHAIN:
        raise ValueError("Mathlib lean-toolchain differs from the core's pinned toolchain")
    mathlib_manifest = mathlib / "lake-manifest.json"
    dependency_lock = package_map(read_json(mathlib_manifest))
    expected_dependencies = {name: value for name, value in locked.items() if name != "mathlib"}
    if dependency_lock.keys() != expected_dependencies.keys():
        raise ValueError("Mathlib dependency names differ from UPSTREAM_LOCK.json")
    for name, package in expected_dependencies.items():
        for field in ("rev", "url", "configFile", "manifestFile"):
            if dependency_lock[name].get(field) != package.get(field):
                raise ValueError(f"Mathlib dependency lock mismatch: {name}.{field}")

    packages_root = args.packages_root.expanduser().resolve() if args.packages_root \
        else (mathlib / ".lake" / "packages").resolve()
    paths = {"mathlib": mathlib}
    paths.update({name: packages_root / name for name in expected_dependencies})
    package_evidence = {}
    local_packages = []
    for name, locked_package in locked.items():
        path = paths[name].resolve()
        if not path.is_dir() or path.is_relative_to(ROOT):
            raise ValueError(f"Existing external package directory required: {name}: {path}")
        config_filename = locked_package["configFile"]
        if Path(config_filename).name != config_filename:
            raise ValueError(f"Invalid configFile in lock: {name}")
        config = path / config_filename
        if not config.is_file():
            raise ValueError(f"Package config missing: {config}")
        head = local_head(path)
        if head is not None and head != locked_package["rev"]:
            raise ValueError(f"Local checkout HEAD mismatch: {name}: {head}")
        package_evidence[name] = {
            "path": str(path), "required_revision": locked_package["rev"],
            "local_git_head": head,
            "revision_evidence": "matching_local_HEAD_metadata" if head else "unavailable",
            "working_tree_and_compiled_cache_verified": False,
            "config_sha256": digest(config),
        }
        local_packages.append({
            "type": "path", "dir": configured_path(path),
            **{field: locked_package[field] for field in (
                "name", "scope", "inherited", "configFile", "manifestFile"
            )},
        })

    compiler = direct_lean(args.lean)
    compiler_evidence = {"status": "not_checked_direct_executable_unavailable"}
    if compiler:
        # Never look up an elan shim on PATH, which could download a toolchain.
        if compiler.stem.lower() == "elan":
            raise ValueError("--lean must identify a direct Lean binary, not elan")
        result = subprocess.run([str(compiler), "--version"], cwd=ROOT,
                                capture_output=True, text=True, timeout=30, check=True)
        version = result.stdout.strip()
        if not re.search(r"\bversion 4\.30\.0(?:,|\s|\))", version) or LEAN_COMMIT not in version:
            raise ValueError(f"Direct Lean binary version/commit mismatch: {version}")
        compiler_evidence = {"status": "version_and_commit_match", "path": str(compiler),
                             "version": version, "binary_content_hash_checked": False}

    config_path = ROOT / "lakefile.toml"
    old_config = config_path.read_text(encoding="utf-8-sig")
    parsed = tomllib.loads(old_config)
    requirements = parsed.get("require", [])
    if len(requirements) != 1 or requirements[0].get("name") != "mathlib":
        raise ValueError("Expected exactly one Mathlib requirement in core lakefile.toml")
    pattern = r"(?ms)^\[\[require\]\][ \t]*\r?\n.*?(?=^\[|\Z)"
    blocks = list(re.finditer(pattern, old_config))
    if len(blocks) != 1:
        raise ValueError("Cannot safely locate the single Mathlib requirement block")
    new_requirement = '[[require]]\nname = "mathlib"\npath = ' + json.dumps(
        configured_path(mathlib), ensure_ascii=True
    ) + "\n\n"
    block = blocks[0]
    new_config = old_config[:block.start()] + new_requirement + old_config[block.end():]
    new_parsed = tomllib.loads(new_config)
    if new_parsed.get("lean_lib") != parsed.get("lean_lib"):
        raise ValueError("Configuration unexpectedly changed Lean library declarations")
    manifest = {"version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": local_packages, "name": parsed["name"], "lakeDir": ".lake"}
    provenance = read_json(ROOT / "SOURCE_PROVENANCE.json")
    report = {
        "kind": "Local configuration metadata; NOT a build or source/cache audit",
        "toolchain": TOOLCHAIN, "lean_commit": LEAN_COMMIT,
        "upstream_lock_sha256": digest(lock_path),
        "mathlib_dependency_manifest_sha256": digest(mathlib_manifest),
        "mathlib_dependency_lock_matches": True,
        "compiler": compiler_evidence, "packages": package_evidence,
        "original_source_inventory_count": len(provenance["modules"]),
        "source_inventory_rehashed": False,
        "source_revision_identity_verified": False,
        "build_performed": False, "network_operations": False,
        "warning": "Matching lock/HEAD metadata does not verify checkout contents or compiled caches.",
    }
    # All validation finishes before the three local output files are replaced.
    atomic_write(config_path, new_config)
    atomic_write(ROOT / "lake-manifest.json", json.dumps(manifest, indent=2) + "\n")
    atomic_write(ROOT / "LOCAL_CONFIGURATION.json", json.dumps(report, indent=2) + "\n")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, required=True,
                        help="Existing Mathlib checkout at the pinned revision")
    parser.add_argument("--packages-root", type=Path,
                        help="Existing sibling package directory; defaults to MATHLIB/.lake/packages")
    parser.add_argument("--lean", type=Path,
                        help="Optional direct Lean executable for --version only; no elan shim")
    args = parser.parse_args()
    try:
        report = configure(args)
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"Configuration rejected: {error}", file=sys.stderr)
        return 1
    print(json.dumps({"configured": str(ROOT), "packages": len(report["packages"]),
                      "compiler_check": report["compiler"]["status"],
                      "build_performed": False, "warning": report["warning"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
