#!/usr/bin/env python3
"""Rebuild/check the proof sources and audit their axiom dependencies.

The negative controls are temporary files. They deliberately contain forbidden
proof mechanisms and must be rejected by Audit.lean; they are never imported by
the mathematical library or retained in the release source tree.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from source_only import check as check_source_only

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "checks" / "results"
RESULTS.mkdir(parents=True, exist_ok=True)


def without_comments_and_strings(text: str) -> str:
    """Remove Lean comments (including nested blocks) and quoted strings."""
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def run(command: list[str], log_name: str, *, success: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    (RESULTS / log_name).write_text(result.stdout)
    if success and result.returncode != 0:
        raise RuntimeError(f"Command failed: {command}\n{result.stdout[-6000:]}")
    return result


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_policy(text: str, relative: str) -> None:
    """Reject trust extensions before elaboration, including kernel-check bypasses."""
    clean = without_comments_and_strings(text)
    for line in re.findall(r"(?m)^\s*import\s+([^\n]+)", clean):
        for name in line.split():
            if not any(name == base or name.startswith(base + ".")
                       for base in ("Hellinger", "Mathlib", "Lean", "Std", "Init")):
                raise RuntimeError(f"Untracked import in proof module {relative}: {name}")
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|implemented_by|extern)\b")
    match = forbidden.search(clean)
    if match:
        raise RuntimeError(f"Forbidden proof token in {relative}: {match.group()}")
    if re.search(r"\b(?:run_cmd|run_tac|elab|macro|initialize|builtin_initialize)\b|#eval", clean):
        raise RuntimeError(f"Unexpected metaprogramming command in proof module {relative}")
    permitted_options = {
        "autoImplicit": {"false"},
        "backward.isDefEq.respectTransparency": {"false", "true"},
    }
    for option, value in re.findall(r"\bset_option\s+(\S+)\s+(\S+)", clean):
        allowed = value in permitted_options.get(option, set())
        if option in {"maxHeartbeats", "maxRecDepth"}:
            allowed = value.isascii() and value.isdecimal()
        if not allowed:
            raise RuntimeError(f"Unapproved Lean option in {relative}: {option} {value}")
    # Also catch qualified or quoted references outside an ordinary set_option command.
    if "skipKernelTC" in clean or "trustLevel" in clean:
        raise RuntimeError(f"Kernel trust override in {relative}")


def main() -> None:
    check_source_only()
    (RESULTS / "verification.json").write_text(json.dumps({
        "status": "running", "started_at": datetime.now(timezone.utc).isoformat()
    }, indent=2) + "\n")
    sources = sorted((ROOT / "Hellinger").rglob("*.lean"))
    protected = [ROOT / "README.md", ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
                 ROOT / "Hellinger.lean", ROOT / "checks/Audit.lean", ROOT / "checks/Replay.lean",
                 Path(__file__).resolve(),
                 *sources, *sorted((ROOT / "checks").glob("*.lean")),
                 *sorted((ROOT / "checks").glob("*.py"))]
    protected = [p for p in protected if p.is_file()]
    before = {p.relative_to(ROOT).as_posix(): digest(p) for p in protected}
    entry = without_comments_and_strings((ROOT / "Hellinger.lean").read_text())
    imports = {name for line in re.findall(r"(?m)^\s*import\s+([^\n]+)", entry)
               for name in line.split()}
    expected_imports = {p.relative_to(ROOT).as_posix().removesuffix(".lean").replace("/", ".")
                        for p in sources}
    if imports != expected_imports:
        raise RuntimeError(f"Entry-point imports differ from proof modules: {imports ^ expected_imports}")
    names: list[dict[str, str]] = []
    source_policy((ROOT / "Hellinger.lean").read_text(), "Hellinger.lean")
    for source in sources:
        relative = source.relative_to(ROOT).as_posix()
        clean = without_comments_and_strings(source.read_text())
        source_policy(source.read_text(), relative)
        for match in re.finditer(r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+(\S+)", clean):
            names.append({"file": relative, "name": match.group(1)})

    version = run(["lake", "env", "lean", "--version"], "lean_version.txt").stdout.strip()
    run(["lake", "build"], "build.log")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    dependencies = {}
    for package in manifest["packages"]:
        directory = ROOT / manifest["packagesDir"] / package["name"]
        actual = run(["git", "-C", str(directory), "rev-parse", "HEAD"],
                     "dependency_" + package["name"] + ".log").stdout.strip()
        dirty = run(["git", "-C", str(directory), "diff", "--name-only", "HEAD"],
                    "dependency_" + package["name"] + "_changes.log").stdout.strip()
        untracked = run(["git", "-C", str(directory), "ls-files", "--others", "--exclude-standard", "--", "*.lean"],
                        "dependency_" + package["name"] + "_untracked_lean.log").stdout.strip()
        if actual != package["rev"] or dirty or untracked:
            raise RuntimeError(f"Dependency does not match its clean pinned revision: {package['name']}")
        dependencies[package["name"]] = {"revision": actual, "tracked_files_clean": True,
                                         "untracked_lean_sources": False}
    mathlib_revision = dependencies["mathlib"]["revision"]
    if f'rev = "{mathlib_revision}"' not in (ROOT / "lakefile.toml").read_text():
        raise RuntimeError("mathlib Lake configuration and lockfile revisions disagree")
    for source in sources:
        relative = source.relative_to(ROOT).as_posix()
        run(["lake", "env", "lean", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true", relative],
            relative.removesuffix(".lean").replace("/", "_") + ".log")
    for check in ("BentQuadraticReview", "RootSemanticsReview"):
        run(["lake", "env", "lean", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true",
             f"checks/{check}.lean"], f"{check}.log")
    audit = run(["lake", "env", "lean", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true", "checks/Audit.lean"], "axiom_audit.log")
    counts = re.search(r"AUDIT_SUCCESS declarations=(\d+) theorems=(\d+)", audit.stdout)
    if not counts:
        raise RuntimeError("Axiom audit did not report successful coverage.")
    if int(counts.group(1)) <= 0 or int(counts.group(2)) <= 0:
        raise RuntimeError("Refusing an empty declaration or theorem audit")
    replay = run(["lake", "env", "lean", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true",
                  "--run", "checks/Replay.lean"], "kernel_replay.log")
    replay_counts = re.search(r"REPLAY_SUCCESS declarations=(\d+) theorems=(\d+) private=(\d+)",
                              replay.stdout)
    if not replay_counts or "REPLAY_NEGATIVE_CONTROL ill_typed_proof=rejected" not in replay.stdout:
        raise RuntimeError("Independent kernel replay or its negative control did not pass")
    if replay_counts.group(1) != counts.group(1) or replay_counts.group(2) != counts.group(2):
        raise RuntimeError("Axiom audit and independent kernel replay cover different project declarations")
    audited_theorems = set(re.findall(r"AUDIT_THEOREM ([^\s:]+):", audit.stdout))
    audited_declarations = set(re.findall(r"AUDIT_DECLARATION ([^\s]+)", audit.stdout))
    if len(audited_declarations) != int(counts.group(1)):
        raise RuntimeError("Axiom audit declaration listing is incomplete or contains duplicates")
    if len(audited_theorems) != int(counts.group(2)) or not audited_theorems <= audited_declarations:
        raise RuntimeError("Theorem listing does not match the audited declaration coverage")
    template = (ROOT / "checks" / "Audit.lean").read_text()
    probes = {
        "custom_axiom": "axiom Hellinger.auditForbidden : False\n",
        "placeholder": "theorem Hellinger.auditPlaceholder : False := by sorry\n",
        "native_evaluation": "theorem Hellinger.auditNative : (1 : Nat) + 1 = 2 := by native_decide\n",
        "private_axiom": "private axiom auditPrivate : False\n",
        "outside_namespace_axiom": "axiom auditOutsideNamespace : False\n",
    }
    guard_results = {"ill_typed_proof": "rejected by independent kernel replay"}
    policy_probes = {
        "kernel_check_bypass": "set_option debug.skipKernelTC true\n",
        "quoted_kernel_check_bypass": "set_option «debug.skipKernelTC» true\n",
        "unknown_option": "set_option auditUnapproved true\n",
        "untracked_import": "import AuditBypass\n",
    }
    for name, text in policy_probes.items():
        try:
            source_policy(text, "negative_control/" + name)
        except RuntimeError as error:
            guard_results[name] = "rejected by source trust policy"
            (RESULTS / ("guard_" + name + ".log")).write_text(str(error) + "\n")
        else:
            raise RuntimeError(f"Source policy failed to reject {name}")
    with tempfile.TemporaryDirectory(prefix="hellinger_audit_") as tmp:
        for name, declaration in probes.items():
            path = Path(tmp) / (name + ".lean")
            path.write_text(template.replace("open Lean Elab Command", declaration + "\nopen Lean Elab Command", 1))
            result = run(["lake", "env", "lean", str(path)], "guard_" + name + ".log", success=False)
            rejected = result.returncode != 0 and "Unapproved axioms" in result.stdout
            if not rejected:
                raise RuntimeError(f"Audit did not reject {name} for the expected reason: {result.stdout[-3000:]}")
            guard_results[name] = "rejected by axiom audit"

    if sorted((ROOT / "Hellinger").rglob("*.lean")) != sources:
        raise RuntimeError("Proof module set changed during verification")
    after = {p.relative_to(ROOT).as_posix(): digest(p) for p in protected}
    if before != after:
        raise RuntimeError("Protected sources changed during verification")
    report = {
        "status": "passed",
        "completed_at": datetime.now(timezone.utc).isoformat(),
        "lean_version": version,
        "mathlib_revision": mathlib_revision,
        "dependency_check": dependencies,
        "proof_modules": [p.relative_to(ROOT).as_posix() for p in sources],
        "source_theorem_lemma_declarations": len(names),
        "source_declarations": names,
        "audited_declarations_including_private_and_generated": int(counts.group(1)),
        "audited_theorems_including_generated": int(counts.group(2)),
        "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"],
        "negative_controls": guard_results,
        "independent_kernel_replay": {
            "status": "passed",
            "declarations": int(replay_counts.group(1)),
            "theorems": int(replay_counts.group(2)),
            "private_declarations": int(replay_counts.group(3)),
            "base_project_modules": 0,
            "ill_typed_proof_control": "rejected",
            "method": "Lean.Environment.replay into a dependencies-only environment; no project declaration preexists",
        },
        "warning_as_error_checks": "all proof modules passed",
        "source_stability": "All protected source hashes unchanged throughout verification",
        "sha256": after,
    }
    (RESULTS / "verification.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ["status", "source_theorem_lemma_declarations",
          "audited_declarations_including_private_and_generated", "negative_controls"]}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    try:
        main()
    except BaseException as error:
        (RESULTS / "verification.json").write_text(json.dumps({
            "status": "failed", "error": str(error),
            "failed_at": datetime.now(timezone.utc).isoformat()
        }, ensure_ascii=False, indent=2) + "\n")
        raise
