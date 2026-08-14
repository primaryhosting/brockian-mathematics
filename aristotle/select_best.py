#!/usr/bin/env python3
"""Select one harvested source per expected target without filename collisions.

Selection prefers a known local compile, then absence of placeholder tokens, then
shorter source.  Remote ``PROVED`` remains candidate provenance; selection itself is
not verification.  ``manifest.json`` is the authoritative target-to-artifact map.
"""
import json
import pathlib
import re

try:
    from proof_identity import (
        artifact_filenames,
        harvested_source_path,
        identity_metadata,
        target_is_represented,
    )
except ModuleNotFoundError:  # imported as a package in tests/tools
    from .proof_identity import (
        artifact_filenames,
        harvested_source_path,
        identity_metadata,
        target_is_represented,
    )

ROOT = pathlib.Path(__file__).resolve().parent
HARVEST = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
VERIFY_STATE = HARVEST / "verify_state.json"
OUT = ROOT / "best_proofs"
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")


def main():
    OUT.mkdir(exist_ok=True)
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    verify_state = json.loads(VERIFY_STATE.read_text()) if VERIFY_STATE.exists() else {}
    compiles = {filename: state.get("compiles") for filename, state in verify_state.items()}

    by_target = {}
    for project_id, meta in ledger.items():
        if meta.get("verdict") != "PROVED":
            continue
        source = harvested_source_path(HARVEST, meta["account"], project_id)
        if source is None:
            continue
        text = source.read_text(errors="ignore")
        body = "\n".join(line for line in text.splitlines() if not line.strip().startswith("--"))
        identity = identity_metadata(text)
        candidate = {
            "file": source,
            "account": meta["account"],
            "project_id": project_id,
            "lines": len(text.splitlines()),
            "placeholder_free": not BAD.search(body),
            "compiles": compiles.get(source.name),
            "identity": identity,
            "target_represented": target_is_represented(meta["target"], identity["declarations"]),
        }
        by_target.setdefault(meta["target"], []).append(candidate)

    def score(candidate):
        return (
            0 if candidate["compiles"] is True else (1 if candidate["compiles"] is None else 2),
            0 if candidate["placeholder_free"] else 1,
            0 if candidate["target_represented"] else 1,
            candidate["lines"],
        )

    artifact_name = artifact_filenames(by_target)
    manifest = {}
    for target, candidates in by_target.items():
        best = min(candidates, key=score)
        artifact = artifact_name[target]
        (OUT / artifact).write_text(best["file"].read_text(errors="ignore"))
        manifest[target] = {
            "artifact_file": artifact,
            "chosen": best["file"].name,
            "account": best["account"],
            "project_id": best["project_id"],
            "lines": best["lines"],
            "placeholder_free": best["placeholder_free"],
            "compiles": best["compiles"],
            "target_represented": best["target_represented"],
            "source_sha256": best["identity"]["source_sha256"],
            "normalized_source_sha256": best["identity"]["normalized_source_sha256"],
            "declarations": best["identity"]["declarations"],
            "n_candidates": len(candidates),
        }
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=1))
    print(
        f"selected one source for {len(manifest)} targets "
        f"(from {sum(len(value) for value in by_target.values())} candidates; "
        f"collision-safe artifacts active)"
    )


if __name__ == "__main__":
    main()
