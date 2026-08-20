"""Tests for scripts/reattest_drain.py — the lazy 4.32.2 attestation migration.

The load-bearing bit is source resolution: the attestation is named by the source FILE
stem, whose namespace may differ (Brockian/AdmissibilityCRT.lean → namespace
Brockian.Admissibility.CRT). If resolution regressed, the drain would silently skip
hundreds of modules."""
import glob
import sys

sys.path.insert(0, "scripts")
import reattest_drain as rd  # noqa: E402


def test_source_path_resolves_every_attestation():
    files = glob.glob("registry/attestations/*.json")
    assert files, "expected attestation files present"
    unresolved = [f for f in files if rd._source_path(f) is None]
    assert unresolved == [], f"{len(unresolved)} attestations have no source: {unresolved[:5]}"


def test_source_path_handles_namespace_vs_filename_divergence():
    # AdmissibilityCRT.json (namespace Brockian.Admissibility.CRT) resolves by file stem
    import os
    p = "registry/attestations/AdmissibilityCRT.json"
    if os.path.exists(p):
        src = rd._source_path(p)
        assert src and src.endswith("AdmissibilityCRT.lean")
