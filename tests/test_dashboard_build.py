"""Tests for aristotle/dashboard_build.py — the Aristotle dashboard data generator.

Fixture-driven per the plan (Chunk 1, Task 1): small inline dicts, NO real data files.
Binding derivation rules live in
docs/superpowers/specs/2026-08-27-aristotle-dashboard-design.md.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "aristotle"))

import dashboard_build as db


# ---------------------------------------------------------------- helpers


def _entry(target, account="admin", verdict="PROVED", tier="T1", **extra):
    e = {"target": target, "account": account, "verdict": verdict, "tier": tier}
    e.update(extra)
    return e


def _build(ledger, axle=None, best_files=None, registry_names=None, inflight=None):
    return db.build_targets(
        ledger,
        axle if axle is not None else {},
        best_files if best_files is not None else set(),
        registry_names if registry_names is not None else set(),
        inflight if inflight is not None else set(),
    )


def _row(rows, target):
    return next(r for r in rows if r["target"] == target)


# ---------------------------------------------------------------- name helpers


def test_domain_of():
    assert db.domain_of("AdditiveComb.cauchy_davenport_Z5") == "AdditiveComb"
    assert db.domain_of("Brockian.Characters5.dft_inversion") == "Brockian"
    assert db.domain_of("nodots") == "(root)"


def test_mangle():
    assert db.mangle("A.b.c") == "A_b_c"
    assert db.mangle("plain") == "plain"


def test_mangle_unicode_matches_select_best_sanitizer():
    """Real pipeline pairs: select_best.py writes best_proofs files via
    re.sub(r"[^A-Za-z0-9]+", "_", target), so unicode chars and adjacent
    separators collapse to ONE underscore. These four targets were stranded
    at stage=candidate (their AXLE results looked like orphans) when mangle
    only mapped dots to underscores."""
    assert db.mangle("BrockianMagnumOpus.φ_pos") == "BrockianMagnumOpus_pos"
    assert db.mangle("Frontier.Q₁_eq_neg_det") == "Frontier_Q_eq_neg_det"
    assert db.mangle("F₂_zero_at_prime") == "F_zero_at_prime"
    assert db.mangle("ω_ne_zero") == "_ne_zero"


def test_unicode_target_joins_axle_result_not_orphaned():
    """End-to-end reproduction of the candidate-strand bug: a unicode-named
    PROVED target whose AXLE file uses the sanitized stem must reach
    verified, and the axle entry must NOT be reported as an orphan."""
    ledger = {"u1": _entry("BrockianMagnumOpus.φ_pos", verdict="PROVED")}
    axle = {"BrockianMagnumOpus_pos.lean": {"verified": True}}
    rows, warnings = _build(ledger, axle=axle,
                            best_files={"BrockianMagnumOpus_pos.lean"})
    assert _row(rows, "BrockianMagnumOpus.φ_pos")["stage"] == "verified"
    assert not any("orphan" in w for w in warnings)


# ---------------------------------------------------------------- dedup


def test_dedup_one_row_per_target_with_account_split():
    ledger = {
        "u1": _entry("Phys.a", account="admin", verdict="PROVED"),
        "u2": _entry("Phys.a", account="chris", verdict="PROVED"),
        "u3": _entry("Phys.a", account="admin", verdict="STOPPED"),
    }
    rows, _ = _build(ledger)
    assert len(rows) == 1
    row = rows[0]
    assert row["target"] == "Phys.a"
    assert row["domain"] == "Phys"
    assert row["submissions"] == 3
    assert row["accounts"] == {"admin": 2, "chris": 1}
    assert row["verdicts"] == {"PROVED": 2, "STOPPED": 1}


def test_extra_ledger_fields_tolerated():
    ledger = {"u1": _entry("QI.x", origin="pipeline", project_name="Frontier Qi")}
    rows, _ = _build(ledger)
    assert rows[0]["target"] == "QI.x"


# ---------------------------------------------------------------- stage ordering


def test_stage_proved_plus_stopped_no_axle_is_candidate():
    ledger = {
        "u%d" % i: _entry("A.t", verdict="PROVED") for i in range(9)
    }
    ledger["u9"] = _entry("A.t", verdict="STOPPED")
    rows, _ = _build(ledger)
    assert rows[0]["stage"] == "candidate"
    assert rows[0]["certificate"] is None


def test_stage_stopped_only():
    ledger = {"u1": _entry("A.t", verdict="STOPPED")}
    rows, _ = _build(ledger)
    assert rows[0]["stage"] == "stopped"


def test_stage_selected_when_best_file_exists():
    ledger = {"u1": _entry("A.t")}
    rows, _ = _build(ledger, best_files={"A_t.lean"})
    assert rows[0]["stage"] == "selected"
    assert rows[0]["certificate"]["file"] == "A_t.lean"
    assert rows[0]["certificate"]["verified"] is None


def test_stage_verified_with_axle_true():
    ledger = {"u1": _entry("A.t")}
    axle = {"A_t.lean": {"verified": True, "environment": "lean-4.32.2",
                         "errors": [], "hash": "abc123"}}
    rows, _ = _build(ledger, axle=axle, best_files={"A_t.lean"})
    row = rows[0]
    assert row["stage"] == "verified"
    assert row["certificate"]["verified"] is True
    assert row["certificate"]["environment"] == "lean-4.32.2"
    assert row["certificate"]["hash"] == "abc123"
    assert row["certificate"]["github_url"].endswith("aristotle/best_proofs/A_t.lean")


def test_stage_verify_failed_never_hidden():
    ledger = {"u1": _entry("A.t")}
    axle = {"A_t.lean": {"verified": False, "environment": "lean-4.32.2",
                         "errors": ["boom"], "hash": "x"}}
    rows, _ = _build(ledger, axle=axle, best_files={"A_t.lean"})
    assert rows[0]["stage"] == "verify_failed"
    assert rows[0]["certificate"]["verified"] is False


def test_stage_axle_null_falls_back_to_selected_with_warning():
    ledger = {"u1": _entry("A.t")}
    axle = {"A_t.lean": {"verified": None, "environment": "lean-4.32.2",
                         "errors": [], "hash": "x"}}
    rows, warnings = _build(ledger, axle=axle, best_files={"A_t.lean"})
    assert rows[0]["stage"] == "selected"
    assert any("null" in w.lower() and "A_t.lean" in w for w in warnings)


def test_stage_attested_beats_verified():
    ledger = {"u1": _entry("A.t")}
    axle = {"A_t.lean": {"verified": True, "environment": "e", "errors": [], "hash": "h"}}
    rows, _ = _build(ledger, axle=axle, best_files={"A_t.lean"},
                     registry_names={"A.t"})
    assert rows[0]["stage"] == "attested"


def test_stage_attested_without_pipeline_certificate():
    ledger = {"u1": _entry("A.t")}
    rows, _ = _build(ledger, registry_names={"A.t"})
    assert rows[0]["stage"] == "attested"
    assert rows[0]["certificate"] is None


def test_stage_in_flight_beats_stopped_but_not_candidate():
    ledger = {
        "u1": _entry("A.stop", verdict="STOPPED"),
        "u2": _entry("A.cand", verdict="PROVED"),
    }
    rows, _ = _build(ledger, inflight={"A.stop", "A.cand"})
    assert _row(rows, "A.stop")["stage"] == "in_flight"
    assert _row(rows, "A.cand")["stage"] == "candidate"


def test_in_flight_only_target_gets_row():
    """A night-submit ID absent from the ledger produces an in_flight row."""
    ledger = {"u1": _entry("A.known")}
    rows, _ = _build(ledger, inflight={"A.pending"})
    row = _row(rows, "A.pending")
    assert row["stage"] == "in_flight"
    assert row["submissions"] == 0
    assert row["verdicts"] == {}


# ---------------------------------------------------------------- in-flight derivation


def test_find_inflight_from_submitted_night_and_log():
    ledger = {"pid-1": _entry("A.done")}
    submitted = {
        "A.done": {"tier": "T1", "ids": [{"account": "admin", "project_id": "pid-1",
                                          "ts": "2026-08-08T22:06:58"}]},
        "A.pending": {"tier": "T1", "ids": [{"account": "chris", "project_id": "pid-2",
                                             "ts": "2026-08-27T18:00:00"}]},
    }
    events = db.parse_night_log([
        "2026-08-27T18:06:00 OK admin B.fresh -> pid-3",
        "2026-08-27T16:58:21 FAIL chris Phys.area_law_1d (RATE)",
    ])
    inflight = db.find_inflight(ledger, submitted, events)
    assert inflight == {"A.pending", "B.fresh"}


# ---------------------------------------------------------------- name join


def test_name_join_dots_to_underscores():
    ledger = {"u1": _entry("A.b.c")}
    axle = {"A_b_c.lean": {"verified": True, "environment": "e", "errors": [], "hash": "h"}}
    rows, _ = _build(ledger, axle=axle, best_files={"A_b_c.lean"})
    assert rows[0]["stage"] == "verified"


def test_orphan_axle_key_warned_and_excluded():
    ledger = {"u1": _entry("A.t")}
    axle = {
        "A_t.lean": {"verified": True, "environment": "e", "errors": [], "hash": "h"},
        "Nobody_home.axck.lean": {"verified": True, "environment": "e",
                                  "errors": [], "hash": "h2"},
    }
    rows, warnings = _build(ledger, axle=axle, best_files={"A_t.lean"})
    assert len(rows) == 1
    assert any("orphan" in w.lower() and "axle" in w.lower() for w in warnings)
    funnel = db.build_funnel(rows, ledger)
    assert funnel["axle_verified"] == 1  # joined targets only, orphan excluded


def test_orphan_best_file_warned():
    ledger = {"u1": _entry("A.t")}
    rows, warnings = _build(ledger, best_files={"A_t.lean", "Stray_file.lean"})
    assert any("orphan" in w.lower() and "best" in w.lower() for w in warnings)
    funnel = db.build_funnel(rows, ledger)
    assert funnel["selected_best"] == 1


# ---------------------------------------------------------------- funnel


def _funnel_fixture():
    ledger = {
        "u1": _entry("A.v", verdict="PROVED"),
        "u2": _entry("A.v", verdict="PROVED", account="chris"),
        "u3": _entry("A.s", verdict="PROVED"),
        "u4": _entry("A.c", verdict="PROVED"),
        "u5": _entry("A.dead", verdict="STOPPED"),
        "u6": _entry("A.f", verdict="PROVED"),
    }
    axle = {
        "A_v.lean": {"verified": True, "environment": "e", "errors": [], "hash": "h"},
        "A_f.lean": {"verified": False, "environment": "e", "errors": ["x"], "hash": "h"},
    }
    best = {"A_v.lean", "A_s.lean", "A_f.lean"}
    return ledger, axle, best


def test_funnel_counts_and_monotonicity():
    ledger, axle, best = _funnel_fixture()
    rows, _ = _build(ledger, axle=axle, best_files=best, registry_names={"A.v"})
    funnel = db.build_funnel(rows, ledger)
    assert funnel["submissions"] == 6
    assert funnel["unique_targets"] == 5
    assert funnel["proved_candidates"] == 5   # submission-level PROVED
    assert funnel["stopped"] == 1
    assert funnel["selected_best"] == 3       # joined targets, not raw files
    assert funnel["axle_verified"] == 1
    assert funnel["axle_failed"] == 1
    assert funnel["registry_attested"] == 1
    assert funnel["riemann_published"] is None
    # by-construction nesting
    assert funnel["submissions"] >= funnel["unique_targets"]
    assert funnel["unique_targets"] >= funnel["selected_best"]
    assert funnel["selected_best"] >= funnel["axle_verified"]
    assert db.funnel_warnings(funnel) == []


def test_registry_crossover_emits_warning_not_failure():
    funnel = {"submissions": 10, "unique_targets": 5, "proved_candidates": 8,
              "stopped": 2, "selected_best": 3, "axle_verified": 1,
              "axle_failed": 0, "registry_attested": 4, "riemann_published": None}
    warns = db.funnel_warnings(funnel)
    assert any("registry" in w.lower() for w in warns)


def test_funnel_with_missing_axle_is_null_not_zero():
    ledger = {"u1": _entry("A.t")}
    rows, warnings = db.build_targets(ledger, None, {"A_t.lean"}, set(), set())
    assert rows[0]["stage"] == "selected"  # degrades, does not crash
    assert any("axle" in w.lower() for w in warnings)
    funnel = db.build_funnel(rows, ledger, missing={"axle"})
    assert funnel["axle_verified"] is None
    assert funnel["axle_failed"] is None


# ---------------------------------------------------------------- yield matrix


def test_multi_tier_target_counted_in_both_cells():
    ledger = {
        "u1": _entry("A.t", tier="FRONTIER-wave2", verdict="PROVED"),
        "u2": _entry("A.t", tier="DOMAIN-math", verdict="PROVED"),
        "u3": _entry("A.t", tier="DOMAIN-math", verdict="PROVED", account="chris"),
        "u4": _entry("A.other", tier="DOMAIN-math", verdict="STOPPED"),
    }
    rows, _ = _build(ledger)
    assert sorted(_row(rows, "A.t")["tiers"]) == ["DOMAIN-math", "FRONTIER-wave2"]
    matrix = db.build_yield_matrix(ledger, verified_targets={"A.t"})
    cells = {(c["domain"], c["tier"]): c for c in matrix}
    assert cells[("A", "FRONTIER-wave2")]["unique"] == 1
    assert cells[("A", "DOMAIN-math")]["unique"] == 2  # A.t deduped per (target, tier)
    assert cells[("A", "FRONTIER-wave2")]["proved_rate"] == 1.0
    assert cells[("A", "FRONTIER-wave2")]["verified_rate"] == 1.0
    assert cells[("A", "DOMAIN-math")]["proved_rate"] == 0.5
    assert cells[("A", "DOMAIN-math")]["stopped_rate"] == 0.5


# ---------------------------------------------------------------- night log / health


def test_parse_night_log_ok_fail_and_junk():
    events = db.parse_night_log([
        "2026-08-27T18:06:00 OK admin CS.barrington -> e8cd9a58",
        "2026-08-27T16:58:21 FAIL chris Phys.area_law_1d (RATE)",
        "Traceback (most recent call last):",
        "",
    ])
    assert len(events) == 2
    assert events[0]["status"] == "OK"
    assert events[0]["project_id"] == "e8cd9a58"
    assert events[1]["status"] == "FAIL"
    assert "RATE" in events[1]["detail"]


def test_rate_limit_count_24h_uses_log_timestamps():
    events = db.parse_night_log([
        "2026-08-25T10:00:00 FAIL chris A.old (RATE)",
        "2026-08-27T10:00:00 FAIL admin A.recent (RATE)",
        "2026-08-27T18:00:00 OK admin A.done -> pid",
        "2026-08-27T17:00:00 FAIL admin A.other (timed out after 300 seconds)",
    ])
    assert db.rate_limit_count_24h(events) == 1  # only A.recent, relative to max ts


def test_build_health_shape():
    events = db.parse_night_log(
        ["2026-08-27T18:06:00 OK admin CS.barrington -> pid%d" % i for i in range(60)]
    )
    ledger = {"u1": _entry("A.t"), "u2": _entry("A.t", account="chris")}
    health = db.build_health(events, ledger, stale_files=["solver_state.json (3w)"],
                             raw_counts={"best_proof_files": 3, "axle_entries": 2},
                             last_harvest_sync="2026-08-27T00:00:00")
    assert len(health["recent_events"]) == 50
    assert health["account_split"] == {"admin": 1, "chris": 1}
    assert health["stale_files"] == ["solver_state.json (3w)"]
    assert health["raw_counts"]["best_proof_files"] == 3
    assert health["last_harvest_sync"] == "2026-08-27T00:00:00"


# ---------------------------------------------------------------- previews


def test_preview_attached_only_for_verified_targets(tmp_path):
    (tmp_path / "A_v.lean").write_text("\n".join("line%d" % i for i in range(30)))
    (tmp_path / "A_f.lean").write_text("failed proof")
    ledger = {"u1": _entry("A.v"), "u2": _entry("A.f")}
    axle = {
        "A_v.lean": {"verified": True, "environment": "e", "errors": [], "hash": "h"},
        "A_f.lean": {"verified": False, "environment": "e", "errors": [], "hash": "h"},
    }
    rows, _ = _build(ledger, axle=axle, best_files={"A_v.lean", "A_f.lean"})
    db.attach_previews(rows, tmp_path)
    v = _row(rows, "A.v")["certificate"]
    f = _row(rows, "A.f")["certificate"]
    assert v["preview"].count("\n") <= 19  # first 20 lines only
    assert v["preview"].startswith("line0")
    assert f["preview"] is None
