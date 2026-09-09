#!/usr/bin/env python3
"""Reject tracked files outside the Lean library and its build/verification tools."""
from pathlib import Path, PurePosixPath
import subprocess

ROOT = Path(__file__).resolve().parent.parent
SUPPORT_FILES = {
    ".gitattributes", ".gitignore", ".github/workflows/lean.yml",
    "README.md", "README.zh-CN.md", "LICENSE", "Hellinger.lean",
    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "checks/Audit.lean", "checks/Replay.lean",
    "checks/BentQuadraticReview.lean", "checks/RootSemanticsReview.lean",
    "checks/verify.py", "checks/source_only.py",
}


def allowed(name: str) -> bool:
    path = PurePosixPath(name)
    return name in SUPPORT_FILES or (
        len(path.parts) >= 2 and path.parts[0] == "Hellinger"
        and path.suffix == ".lean" and ".." not in path.parts
    )


def check() -> None:
    result = subprocess.run(
        ["git", "ls-files", "-z"], cwd=ROOT, check=True, capture_output=True
    )
    names = result.stdout.decode().rstrip("\0").split("\0")
    rejected = [name for name in names if not allowed(name)]
    if rejected:
        raise RuntimeError(f"Files outside the source-only scope: {rejected}")
    if not SUPPORT_FILES <= set(names):
        raise RuntimeError(f"Missing support files: {sorted(SUPPORT_FILES - set(names))}")
    for name in names:
        path = ROOT / name
        if path.is_symlink() or not path.is_file():
            raise RuntimeError(f"Expected a regular source file: {name}")
        text = path.read_text(encoding="utf-8")
        if "\0" in text or text.startswith(("%PDF-", "PK\x03\x04")):
            raise RuntimeError(f"Unexpected binary payload: {name}")
    print(f"SOURCE_ONLY_SUCCESS files={len(names)}")


if __name__ == "__main__":
    check()
