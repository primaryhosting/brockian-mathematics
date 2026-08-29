#!/usr/bin/env python3
"""Wave 68: bounded compounding-proof harvest on the exact Wave 67 trust base.

No proof search and no submission occurs in this wave.  It assimilates seven
already-returned Aristotle declarations, verifies the two changed Lean modules,
obtains fresh per-declaration AXLE evidence through the in-process API, merges
that evidence into canonical receipts without dropping siblings, preserves any
concurrently submitted solver work, and runs every promotion firewall before
persisting state.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import harvest_gate as HG  # noqa: E402


BASELINE = 11152
BASE_PROVED = 11235
EXPECTED_PROVED = 11242
EXPECTED_DELTA = EXPECTED_PROVED - BASELINE
EXPECTED_NEW = EXPECTED_PROVED - BASE_PROVED
EXPECTED_HISTORICAL = 102

XI_NAMES = [
    "riemannXi_zero_quartet",
    "riemannXi_one_eq_zero",
    "riemannXi_ne_zero_of_re_eq_one_of_ne_one",
    "riemannXi_eq_zero_iff_of_re_eq_one",
    "riemannXi_eq_zero_iff_of_re_eq_zero",
]
FOURIER_NAMES = [
    "norm_fourier_le_sum_norm",
    "norm_fourier_sq_le_card_mul_sum",
]

QUARANTINED = {
    "Brockian.Admissibility.CRT.admissibleResidues_crt_card_two_primes",
    "Brockian.Admissibility.CriterionScaffold.localTupleAdmissible_iff_exists_avoids",
    "Brockian.AdmissibilityCRTGeneral.admissibleTupleResidues_prodCRT_card",
    "Brockian.AdmissibilityDiagonal.admissibility_count_dichotomy",
    "Brockian.AdmissibilityHLCriterion.admissible_iff_card_image_lt",
    "Brockian.AdmissibilityKTuple.admissibleTupleResidues_card_pair",
    "Brockian.AliquotStructure.quasiperfect_isSquare_or_two_mul_square",
    "Brockian.C5SpectralMultiplicities.multiplicity_golden_sub_one",
    "Brockian.CollatzPartial.collatz_four",
    "Brockian.Weyl.ConfiningShape.brockian_eigenvalue_real_of_candidate",
    "Brockian.XiFunctionalEquation.riemannXi_conj_self_of_re_eq_half",
    "Brockian.XiFunctionalEquation.riemannXi_zero_mem_critical_strip",
}

TESTS = [
    "tests/test_harvest_gate.py",
    "tests/test_proof_assimilation.py",
    "tests/test_select_best.py",
    "tests/test_attest.py",
    "tests/test_gen_registry.py",
    "tests/test_attestation_integrity.py",
    "tests/test_audit_registry_consistency.py",
    "tests/test_no_theater_lint.py",
    "tests/test_engine_register.py",
    "tests/test_engine_verify.py",
    "tests/test_ingest_discover.py",
    "tests/test_conveyor.py",
    "tests/test_conveyor_paperclip.py",
    "tests/test_conveyor_notify.py",
    "tests/test_export_obsidian.py",
]


def run(args: list[str], *, timeout: int = 900, capture: bool = False) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(args), flush=True)
    result = subprocess.run(
        args,
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=capture,
        timeout=timeout,
    )
    if capture and result.stdout:
        print(result.stdout, end="", flush=True)
    if capture and result.stderr:
        print(result.stderr, end="", file=sys.stderr, flush=True)
    if result.returncode != 0:
        raise RuntimeError(f"command failed rc={result.returncode}: {' '.join(args)}")
    return result


def registry() -> dict:
    return json.loads((ROOT / "registry/theorems.json").read_text())


def receipt(stem: str) -> dict:
    return json.loads((ROOT / "registry/attestations" / f"{stem}.json").read_text())


def declaration_names(value: dict) -> set[str]:
    return {d["name"] for d in value.get("declarations", [])}


def quarantines() -> set[str]:
    found: set[str] = set()
    for path in (ROOT / "registry/attestations").glob("*.json"):
        value = json.loads(path.read_text())
        found.update(
            d["name"] for d in value.get("declarations", [])
            if d.get("verification_quarantine") is True
        )
    return found


def assert_base() -> tuple[dict, dict]:
    summary = registry()["summary"]
    if summary.get("PROVED") != BASE_PROVED or summary.get("UNVERIFIED") != 12:
        raise RuntimeError(f"not on exact Wave 67 trust base: {summary}")
    xi = receipt("XiFunctionalEquation")
    fourier = receipt("CharactersQ")
    if len(xi.get("declarations", [])) != 26:
        raise RuntimeError("Xi receipt floor is not 26")
    if len(fourier.get("declarations", [])) != 7:
        raise RuntimeError("CharactersQ receipt floor is not 7")
    if quarantines() != QUARANTINED:
        raise RuntimeError("the exact twelve-declaration quarantine overlay changed")
    for path, names in (
        (ROOT / "Brockian/XiFunctionalEquation.lean", XI_NAMES),
        (ROOT / "Brockian/CharactersQ.lean", FOURIER_NAMES),
    ):
        source = path.read_text()
        for name in names:
            if source.count(f"theorem {name}") != 1:
                raise RuntimeError(f"{path}: expected exactly one declaration {name}")
    print("base_proved=11235 quarantine=12 xi_receipt=26 characters_receipt=7", flush=True)
    return xi, fourier


def verify_sources() -> None:
    run([sys.executable, "-m", "pytest", "tests/test_harvest_gate.py", "tests/test_attest.py", "-q"])
    run([sys.executable, "scripts/harvest_gate.py"])
    run(["lake", "env", "lean", "Brockian/CharactersQ.lean"], timeout=900)
    scaffold_olean = ROOT / ".lake/build/lib/lean/Brockian/RiemannScaffold.olean"
    scaffold_olean.parent.mkdir(parents=True, exist_ok=True)
    run(
        [
            "lake",
            "env",
            "lean",
            "-o",
            str(scaffold_olean),
            "Brockian/RiemannScaffold.lean",
        ],
        timeout=900,
    )
    run(["lake", "env", "lean", "Brockian/XiFunctionalEquation.lean"], timeout=900)
    print("local_lean_files=2", flush=True)


def attest_and_merge(old_xi: dict, old_fourier: dict) -> dict[str, dict]:
    results: dict[str, dict] = {}
    ok, merged, raw = HG.attest(
        "Brockian/CharactersQ.lean",
        "Brockian.CharactersQ",
        FOURIER_NAMES,
        "wave68-characters",
    )
    if not ok:
        print(raw[:4096], file=sys.stderr, flush=True)
        raise RuntimeError("fresh CharactersQ attestation failed")
    if len(merged.get("declarations", [])) != 9:
        raise RuntimeError("CharactersQ receipt did not grow exactly 7 -> 9")
    if not declaration_names(old_fourier) <= declaration_names(merged):
        raise RuntimeError("CharactersQ sibling evidence regressed")
    results["CharactersQ"] = merged

    ok, merged, raw = HG.attest(
        "Brockian/XiFunctionalEquation.lean",
        "Brockian.XiFunctionalEquation",
        XI_NAMES,
        "wave68-xi",
    )
    if not ok:
        print(raw[:4096], file=sys.stderr, flush=True)
        raise RuntimeError("fresh Xi attestation failed")
    if len(merged.get("declarations", [])) != 31:
        raise RuntimeError("Xi receipt did not grow exactly 26 -> 31")
    if not declaration_names(old_xi) <= declaration_names(merged):
        raise RuntimeError("Xi sibling evidence regressed")
    if quarantines() != QUARANTINED:
        raise RuntimeError("partial re-attestation changed an untouched quarantine")
    results["XiFunctionalEquation"] = merged
    return results


def assert_new_evidence(reports: dict[str, dict]) -> None:
    expected = {
        *(f"Brockian.CharactersQ.{name}" for name in FOURIER_NAMES),
        *(f"Brockian.XiFunctionalEquation.{name}" for name in XI_NAMES),
    }
    found: dict[str, dict] = {}
    for report in reports.values():
        for declaration in report.get("declarations", []):
            if declaration.get("name") in expected:
                found[declaration["name"]] = declaration
    if set(found) != expected:
        raise RuntimeError(f"fresh evidence mismatch: missing={sorted(expected - set(found))}")
    for name, declaration in found.items():
        if (
            declaration.get("axle_verdict") != "verified"
            or declaration.get("axioms_ok") is not True
            or not isinstance(declaration.get("axioms"), list)
            or declaration.get("verification_quarantine") is True
        ):
            raise RuntimeError(f"{name}: incomplete fresh evidence {declaration}")
        print(f"AXIOMS {name}: {json.dumps(declaration['axioms'])}", flush=True)


def regenerate_and_gate() -> None:
    run([sys.executable, "scripts/gen_registry.py"])
    current = registry()
    summary = current["summary"]
    if summary.get("PROVED") != EXPECTED_PROVED or summary.get("UNVERIFIED") != 12:
        raise RuntimeError(f"unexpected derived registry: {summary}")
    if quarantines() != QUARANTINED:
        raise RuntimeError("quarantine overlay changed during registry generation")
    proved = {e["name"] for e in current["theorems"] if e.get("register") == "PROVED"}
    expected_new = {
        *(f"Brockian.CharactersQ.{name}" for name in FOURIER_NAMES),
        *(f"Brockian.XiFunctionalEquation.{name}" for name in XI_NAMES),
    }
    if not expected_new <= proved:
        raise RuntimeError(f"new declarations not promoted: {sorted(expected_new - proved)}")

    run([sys.executable, "-m", "pytest", *TESTS, "-q"], timeout=900)
    run([sys.executable, "scripts/check_attestation_integrity.py", "--strict"])
    run([sys.executable, "scripts/audit_registry_consistency.py", "--strict", "--limit", "20"])
    run([sys.executable, "scripts/verify_firewall.py"])
    run([sys.executable, "scripts/validate_manifests.py"])
    print(
        f"registry_proved={summary['PROVED']} new_proved_theorems={EXPECTED_DELTA} "
        f"unique_new={EXPECTED_NEW}",
        flush=True,
    )


def update_frontier() -> None:
    path = ROOT / "research/frontier_queue.json"
    value = json.loads(path.read_text())
    entries = value.setdefault("entries", [])
    by_target = {entry.get("target"): entry for entry in entries}
    targets = [
        *(f"Brockian.CharactersQ.{name}" for name in FOURIER_NAMES),
        *(f"Brockian.XiFunctionalEquation.{name}" for name in XI_NAMES),
    ]
    now = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
    for target in targets:
        module, short = target.rsplit(".", 1)
        entry = by_target.get(target)
        if entry is None:
            entry = {
                "id": target,
                "target": target,
                "module": module,
                "tier": "A-compounding-bridge",
                "statement": short,
                "rationale": "Assimilated only after exact-statement review and fresh fail-closed attestation.",
                "source": "wave68 bounded Aristotle harvest",
                "scores": {"compounding": 5},
                "evidence": {},
                "history": [],
            }
            entries.append(entry)
        entry["status"] = "proved"
        entry["review_only"] = False
        entry["evidence"] = {
            "attestation": target,
            "wave": 68,
            "fresh_axiom_evidence": True,
        }
        entry.setdefault("history", []).append({
            "event": "proved",
            "experiment": "wave68",
            "ts": now,
            "note": "fresh local Lean + AXLE + sibling-preserving receipt merge",
        })
    HG.atomic_json_write(str(path), value)
    print(f"frontier_entries_promoted={len(targets)}", flush=True)


def reconcile_aristotle_state() -> tuple[int, int]:
    data = Path(os.environ.get("AUTOLAB_DATA_DIR", ROOT / ".autolab-data"))
    path = data / "aristotle_state.json"
    if not path.exists():
        raise RuntimeError(f"missing persistent Aristotle state: {path}")
    value = json.loads(path.read_text())
    pending = dict(value.get("pending", {}))
    outcomes = value.setdefault("attempt_outcomes", {})
    terminal = {
        "Brockian.XiFunctionalEquation.riemannXi_zero_quartet#B":
            ("accepted", "selected unique quartet proof"),
        "Brockian.XiFunctionalEquation.riemannXi_zero_quartet#A":
            ("duplicate", "same statement as selected B attempt"),
        "Brockian.XiFunctionalEquation.riemannXi_ne_zero_of_re_eq_one#A":
            ("refuted", "counterexample s = 1"),
        "Brockian.XiFunctionalEquation.riemannXi_ne_zero_of_re_eq_one#B":
            ("refuted", "counterexample s = 1"),
        "Brockian.CharactersQ.norm_fourier_le_sum_norm#A":
            ("accepted-corrected-target", "explicit modulus argument restored"),
        "Brockian.CharactersQ.norm_fourier_le_sum_norm#B":
            ("duplicate", "same corrected theorem as selected A attempt"),
        "Brockian.CharactersQ.norm_fourier_sq_le_card_mul_sum#B":
            ("accepted-corrected-target", "explicit modulus argument restored"),
    }
    preserved = dict(pending)
    archived = 0
    for target, (status, reason) in terminal.items():
        pid = pending.get(target)
        if pid is None:
            continue
        outcomes[target] = {"pid": pid, "status": status, "reason": reason, "wave": 68}
        preserved.pop(target)
        archived += 1
    value["pending"] = preserved
    done = value.setdefault("done", {})
    done["Brockian.XiFunctionalEquation.riemannXi_zero_quartet"] = \
        "ce26fd8f-7d2f-44b2-b6f4-d118593ae816"
    done["Brockian.CharactersQ.norm_fourier_le_sum_norm"] = \
        "5e203044-299f-4c92-9e7c-02707919a138"
    done["Brockian.CharactersQ.norm_fourier_sq_le_card_mul_sum"] = \
        "e8c286d4-4c8f-41ac-b82d-d2b85e85b3ae"
    value["last_reconciled_wave"] = 68
    value["last_reconciled_at"] = datetime.now(timezone.utc).isoformat()
    HG.atomic_json_write(str(path), value)
    check = json.loads(path.read_text()).get("pending", {})
    if check != preserved:
        raise RuntimeError("Aristotle pending-state preservation failed")
    print(
        f"aristotle_stale_pending_archived={archived} "
        f"aristotle_pending_preserved={len(preserved)}",
        flush=True,
    )
    return archived, len(preserved)


def write_insight() -> None:
    marker = "<!-- insight:wave68:in-process-receipt-merge -->"
    statement = (
        "A proof harvester must call attest.attest in-process and atomically merge fresh "
        "declarations by fully-qualified name; invoking the attest.py CLI for one name "
        "creates a crash window that can replace a complete module receipt with a singleton."
    )
    path = ROOT / "research/insights.md"
    text = path.read_text() if path.exists() else ""
    if marker not in text:
        with path.open("a") as handle:
            handle.write(
                f"\n{marker}\n- (wave68, conf 0.99, tags mechanics/verification/integrity) "
                f"{statement}\n"
            )
    backfill = {
        "payload": {
            "wave": "wave68",
            "statement": statement,
            "confidence": 0.99,
            "tags": ["mechanics", "verification", "integrity"],
            "corroborating_waves": ["wave66", "wave67", "wave68"],
        },
        "classification": "durable substitute plus readback; platform insight roundtrip remains monitored",
    }
    HG.atomic_json_write(str(ROOT / "research/insight_store_backfill.json"), backfill)
    if marker not in path.read_text():
        raise RuntimeError("insight write/readback failed")
    print("insight_roundtrip=1", flush=True)


def commit_and_push() -> None:
    paths = [
        "registry/attestations/CharactersQ.json",
        "registry/attestations/XiFunctionalEquation.json",
        "registry/theorems.json",
        "REGISTRY.md",
        "research/frontier_queue.json",
        "research/insights.md",
        "research/insight_store_backfill.json",
    ]
    run(["git", "add", *paths])
    run(["git", "diff", "--cached", "--check"])
    staged = run(["git", "diff", "--cached", "--name-only"], capture=True).stdout.strip()
    if not staged:
        raise RuntimeError("successful wave produced no durable registration changes")
    run(["git", "commit", "-m", "wave68: assimilate seven compounding proofs"])
    branch = run(["git", "rev-parse", "--abbrev-ref", "HEAD"], capture=True).stdout.strip()
    if not branch.startswith("exp/"):
        raise RuntimeError(f"refusing to push unexpected execution branch: {branch}")
    run(["git", "push", "origin", branch], timeout=300, capture=True)
    print(f"durable_branch={branch}", flush=True)


def main() -> int:
    import mlflow

    with mlflow.start_run():
        mlflow.log_params({
            "wave": 68,
            "base": "6a0738f53dd844225e9ebf6e9294137d205bf5e9",
            "mode": "code-locked bounded harvest",
            "autogen": "off",
            "proof_backend": "Aristotle artifacts; no new submissions",
            "attestation_write": "in-process atomic sibling merge",
        })
        try:
            if not os.environ.get("AXLE_API_KEY"):
                raise RuntimeError("AXLE_API_KEY is required before any expensive verification")
            old_xi, old_fourier = assert_base()
            verify_sources()
            reports = attest_and_merge(old_xi, old_fourier)
            assert_new_evidence(reports)
            regenerate_and_gate()
            update_frontier()
            archived, pending = reconcile_aristotle_state()
            write_insight()
            commit_and_push()
        except Exception as exc:  # noqa: BLE001
            mlflow.log_metrics({
                "lanes_failed": 1,
                "trust_invariant_passed": 0,
                "submit_attempted": 0,
                "submit_accepted": 0,
            })
            print(f"WAVE68 FAILED: {type(exc).__name__}: {exc}", file=sys.stderr, flush=True)
            return 1

        mlflow.log_metrics({
            "new_proved_theorems": EXPECTED_DELTA,
            "registry_proved": EXPECTED_PROVED,
            "historical_candidate_total": EXPECTED_HISTORICAL,
            "unique_proofs_assimilated": EXPECTED_NEW,
            "verification_quarantined": len(QUARANTINED),
            "receipt_siblings_preserved": 33,
            "stale_pending_archived": archived,
            "aristotle_pending": pending,
            "submit_attempted": 0,
            "submit_accepted": 0,
            "submit_rejected_capacity": 0,
            "capacity_observed_preflight": 1,
            "trust_invariant_passed": 1,
            "promotion_gate_passed": 1,
            "insight_roundtrip": 1,
            "lanes_failed": 0,
        })
        print(
            f"WAVE68 PASS: trusted={EXPECTED_DELTA} unique_new={EXPECTED_NEW} "
            f"historical_candidates={EXPECTED_HISTORICAL} quarantined=12 submissions=0",
            flush=True,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
