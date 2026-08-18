"""Tests for the Conveyor publish + notify legs (aristotle/conveyor_notify.py).

Covers exactly what the spec demands:
  - daily digest boundary logic (first cycle after 6am, once per day, baseline)
  - Today approval-card idempotency (state guard + receipt_id + pending retry)
  - draft-prompt generation HONESTY (counts must equal the registry values,
    exact new theorem names, lake_build-pending posture stated, no overclaim)
"""
import datetime
import json

import pytest

from aristotle import conveyor, conveyor_notify


@pytest.fixture(autouse=True)
def _isolated_log(tmp_path, monkeypatch):
    """Never write test noise into the real aristotle/conveyor.log."""
    monkeypatch.setattr(conveyor, "LOG", str(tmp_path / "conveyor.test.log"))


# ---------------------------------------------------------------- fixtures

def write_registry(tmp_path, proved_names, lake_pending=None, extra=None):
    """A miniature registry/theorems.json in the real generated shape."""
    lake_pending = set(lake_pending if lake_pending is not None else proved_names)
    theorems = []
    for n in proved_names:
        theorems.append({
            "name": n, "register": "PROVED",
            "verification": {
                "lake_build": "pending" if n in lake_pending else "verified",
                "axle": {"verdict": "verified"},
            },
        })
    for t in (extra or []):
        theorems.append(t)
    reg = {
        "generated_from": "AXLE attestations",
        "summary": {"PROVED": len(proved_names)},
        "theorems": theorems,
    }
    p = tmp_path / "theorems.json"
    p.write_text(json.dumps(reg))
    return str(p)


class RecordingPoster:
    def __init__(self, fail=False):
        self.calls = []
        self.fail = fail

    def __call__(self, payload, **kw):
        self.calls.append(payload)
        if self.fail:
            return None
        return {"id": f"gate-{len(self.calls)}", "status": "pending"}


def never_probes(receipt_id, **kw):
    return False


# ---------------------------------------------------------------- registry snapshot

def test_snapshot_reads_counts_and_names_from_registry(tmp_path):
    path = write_registry(tmp_path, ["Brockian.A.a", "Brockian.B.b"])
    snap = conveyor_notify.registry_proved_snapshot(path)
    assert snap["count"] == 2
    assert snap["names"] == {"Brockian.A.a", "Brockian.B.b"}
    assert snap["lake_build"] == {"pending": 2}
    assert snap["total"] == 2


def test_snapshot_missing_registry_is_none_not_zero(tmp_path):
    assert conveyor_notify.registry_proved_snapshot(
        str(tmp_path / "nope.json")) is None


# ---------------------------------------------------------------- prompt honesty

def two_snapshots(tmp_path):
    before = conveyor_notify.registry_proved_snapshot(
        write_registry(tmp_path, ["Brockian.Old.x", "Brockian.Old.y"]))
    (tmp_path / "theorems.json").unlink()
    after = conveyor_notify.registry_proved_snapshot(
        write_registry(tmp_path, ["Brockian.Old.x", "Brockian.Old.y",
                                  "Brockian.New.thm1", "Brockian.New.thm2"]))
    return before, after


def test_prompt_counts_equal_registry_values(tmp_path):
    before, after = two_snapshots(tmp_path)
    prompt = conveyor_notify.build_draft_prompt(before, after)
    # counts in the prompt ARE the registry summary values — no other source
    assert "2 -> 4" in prompt
    assert "registry/theorems.json" in prompt


def test_prompt_names_exact_new_theorems_only(tmp_path):
    before, after = two_snapshots(tmp_path)
    prompt = conveyor_notify.build_draft_prompt(before, after)
    assert "- Brockian.New.thm1" in prompt
    assert "- Brockian.New.thm2" in prompt
    # pre-existing names are NOT presented as new
    assert "- Brockian.Old.x" not in prompt


def test_prompt_states_lake_build_pending_posture(tmp_path):
    before, after = two_snapshots(tmp_path)
    prompt = conveyor_notify.build_draft_prompt(before, after)
    assert "lake build" in prompt.lower() or "lake_build" in prompt.lower()
    assert f"pending for {after['lake_build']['pending']} of {after['total']}" \
        in prompt
    assert "AXLE-attested" in prompt
    assert "do not publish or deploy" in prompt.lower()


def test_prompt_reports_removed_proved_entries_honestly(tmp_path):
    before = conveyor_notify.registry_proved_snapshot(
        write_registry(tmp_path, ["Brockian.Gone.z", "Brockian.Keep.k"]))
    (tmp_path / "theorems.json").unlink()
    after = conveyor_notify.registry_proved_snapshot(
        write_registry(tmp_path, ["Brockian.Keep.k"]))
    prompt = conveyor_notify.build_draft_prompt(before, after)
    assert "Brockian.Gone.z" in prompt
    assert "left the PROVED register" in prompt


def test_prompt_truncates_but_admits_truncation(tmp_path):
    before = conveyor_notify.registry_proved_snapshot(
        write_registry(tmp_path, []))
    (tmp_path / "theorems.json").unlink()
    names = [f"Brockian.Bulk.t{i:03d}" for i in range(50)]
    after = conveyor_notify.registry_proved_snapshot(
        write_registry(tmp_path, names))
    prompt = conveyor_notify.build_draft_prompt(before, after, max_names=40)
    assert "...and 10 more newly PROVED entries" in prompt


def test_draft_receipt_is_deterministic():
    a = conveyor_notify.draft_receipt_id(2, 4, ["X", "Y"])
    b = conveyor_notify.draft_receipt_id(2, 4, ["Y", "X"])
    c = conveyor_notify.draft_receipt_id(2, 5, ["X", "Y"])
    assert a == b
    assert a != c


# ---------------------------------------------------------------- draft leg wiring

def test_proved_draft_queued_once_and_card_posted(tmp_path):
    before, after = two_snapshots(tmp_path)
    state, cycle = {}, {}
    sent = []
    card_poster = RecordingPoster()
    queued = conveyor.maybe_queue_proved_draft(
        state, cycle, before, after,
        poster=lambda p, **kw: sent.append(p) or True,
        card_poster=card_poster, card_prober=never_probes,
        state_path=str(tmp_path / "state.json"))
    assert queued is True
    assert len(sent) == 1 and "Brockian.New.thm1" in sent[0]
    assert cycle["lovable_drafts_queued"] == 1
    assert cycle["approval_cards_posted"] == 1
    meta = card_poster.calls[0]["metadata"]
    assert meta["event"] == "lovable_draft_ready"
    assert meta["receipt_id"].startswith("conveyor_draft_")
    assert meta["proved_before"] == 2 and meta["proved_after"] == 4

    # same snapshots again -> guard blocks BOTH the prompt and the card
    again = conveyor.maybe_queue_proved_draft(
        state, {}, before, after,
        poster=lambda p, **kw: sent.append(p) or True,
        card_poster=card_poster, card_prober=never_probes,
        state_path=str(tmp_path / "state.json"))
    assert again is False
    assert len(sent) == 1 and len(card_poster.calls) == 1


def test_no_draft_when_count_unchanged_or_registry_unreadable(tmp_path):
    before, _ = two_snapshots(tmp_path)
    sp = str(tmp_path / "state.json")
    assert conveyor.maybe_queue_proved_draft(
        {}, {}, before, before, poster=lambda p, **kw: True,
        state_path=sp) is False
    assert conveyor.maybe_queue_proved_draft(
        {}, {}, None, before, poster=lambda p, **kw: True,
        state_path=sp) is False
    assert conveyor.maybe_queue_proved_draft(
        {}, {}, before, None, poster=lambda p, **kw: True,
        state_path=sp) is False


# ---------------------------------------------------------------- card idempotency

def test_card_posted_exactly_once_per_receipt(tmp_path):
    state = {}
    poster = RecordingPoster()
    payload = conveyor_notify.build_attest_failure_gate("r1", "stage failed")
    assert conveyor_notify.post_approval_card(
        state, "r1", payload, poster=poster, prober=never_probes,
        state_path=str(tmp_path / "s.json")) is True
    assert conveyor_notify.post_approval_card(
        state, "r1", payload, poster=poster, prober=never_probes,
        state_path=str(tmp_path / "s.json")) is False
    assert len(poster.calls) == 1
    assert state["approval_cards"]["r1"]["gate_id"] == "gate-1"


def test_card_failure_queues_pending_then_flush_delivers_once(tmp_path):
    state = {}
    down = RecordingPoster(fail=True)
    payload = conveyor_notify.build_draft_ready_gate(
        "r2", {"count": 1, "names": set(), "lake_build": {}, "total": 1},
        {"count": 2, "names": {"T"}, "lake_build": {"pending": 2}, "total": 2},
        ["T"])
    assert conveyor_notify.post_approval_card(
        state, "r2", payload, poster=down, prober=never_probes) is False
    assert [p["receipt_id"] for p in state["pending_approval_cards"]] == ["r2"]
    # while pending, a repeat attempt neither posts nor duplicates the queue
    assert conveyor_notify.post_approval_card(
        state, "r2", payload, poster=down, prober=never_probes) is False
    assert len(state["pending_approval_cards"]) == 1

    up = RecordingPoster()
    delivered = conveyor_notify.flush_pending_approval_cards(
        state, poster=up, prober=never_probes,
        state_path=str(tmp_path / "s.json"))
    assert delivered == 1
    assert state["pending_approval_cards"] == []
    # flushed card is now guarded like any other
    assert conveyor_notify.post_approval_card(
        state, "r2", payload, poster=up, prober=never_probes) is False
    assert len(up.calls) == 1


def test_serverside_probe_prevents_duplicate_after_state_loss(tmp_path):
    state = {}  # fresh state — simulates a lost conveyor_state.json
    poster = RecordingPoster()
    assert conveyor_notify.post_approval_card(
        state, "r3", {"title": "x"}, poster=poster,
        prober=lambda rid, **kw: True,
        state_path=str(tmp_path / "s.json")) is False
    assert poster.calls == []
    assert state["approval_cards"]["r3"]["note"] == "found serverside"


def test_gate_row_shape_matches_existing_writers():
    """Row shape must match the shape the ACUTIS readers/PATCHers use
    (routes/missions.js select + conscious_state/delegation_executor inserts)."""
    for payload in (
        conveyor_notify.build_attest_failure_gate("rid", "why"),
        conveyor_notify.build_draft_ready_gate(
            "rid", {"count": 0, "names": set(), "lake_build": {}, "total": 0},
            {"count": 1, "names": {"N"}, "lake_build": {"pending": 1},
             "total": 1}, ["N"]),
    ):
        assert payload["status"] == "pending"
        assert set(payload) >= {"gate_type", "title", "description",
                                "requested_by", "risk_level", "status",
                                "metadata"}
        assert payload["metadata"]["receipt_id"] == "rid"
        assert payload["metadata"]["source"] == "aristotle_conveyor"


def test_attest_failure_card_skips_deferral_and_dedupes(tmp_path):
    state = {}
    poster = RecordingPoster()
    sp = str(tmp_path / "s.json")
    deferred = {"stopped_reason": conveyor.DEFERRED_REASON}
    assert conveyor.maybe_post_attest_failure_card(
        state, deferred, "fp", card_poster=poster,
        card_prober=never_probes, state_path=sp) is False
    assert poster.calls == []

    failing = {"stopped_reason": "stage axle_verify failed (rc=1)",
               "stages": [{"name": "axle_verify", "tail": "boom"}]}
    assert conveyor.maybe_post_attest_failure_card(
        state, dict(failing), "fp",
        card_poster=poster, card_prober=never_probes, state_path=sp) is True
    # identical failure signature next cycle -> no second card
    assert conveyor.maybe_post_attest_failure_card(
        state, dict(failing), "fp",
        card_poster=poster, card_prober=never_probes, state_path=sp) is False
    assert len(poster.calls) == 1
    assert poster.calls[0]["metadata"]["event"] == "attest_failure"
    # a DIFFERENT failure posts its own card
    assert conveyor.maybe_post_attest_failure_card(
        state, {"stopped_reason": "audit_registry_consistency --strict failed"},
        "fp",
        card_poster=poster, card_prober=never_probes, state_path=sp) is True
    assert len(poster.calls) == 2
    # ...and so does the SAME reason on a NEW attestation fingerprint
    assert conveyor.maybe_post_attest_failure_card(
        state, dict(failing), "fp2",
        card_poster=poster, card_prober=never_probes, state_path=sp) is True
    assert len(poster.calls) == 3


def test_attest_failure_receipt_ignores_consumed_receipts(tmp_path):
    """Regression: run_cycle step 3 advances processed_receipt_ids on
    chain_ok even when the registry hop fails the truth gate, so the retry
    cycle sees digests=[]. The receipt must therefore cover ONLY
    (reason, fingerprint) — otherwise the identical failure posts a second
    Today card across the receipts-consumed boundary."""
    rid = conveyor_notify.attest_failure_receipt_id(
        "hop stage audit failed (rc=1)", "fp")
    # deterministic, and there is no receipts input to vary
    assert rid == conveyor_notify.attest_failure_receipt_id(
        "hop stage audit failed (rc=1)", "fp")
    assert rid != conveyor_notify.attest_failure_receipt_id(
        "hop stage audit failed (rc=1)", "fp2")
    assert rid != conveyor_notify.attest_failure_receipt_id(
        "other reason", "fp")

    # end-to-end across the boundary: cycle 1 (digests consumed) then cycle 2
    # (digests empty, same reason + fp) -> exactly one card
    state, poster = {}, RecordingPoster()
    sp = str(tmp_path / "s.json")
    failing = {"stopped_reason": "hop stage audit failed (rc=1)"}
    assert conveyor.maybe_post_attest_failure_card(
        state, dict(failing), "fp", card_poster=poster,
        card_prober=never_probes, state_path=sp) is True
    assert conveyor.maybe_post_attest_failure_card(
        state, dict(failing), "fp", card_poster=poster,
        card_prober=never_probes, state_path=sp) is False
    assert len(poster.calls) == 1


# ---------------------------------------------------------------- digest boundary

def T(h, m=0, day=15):
    return datetime.datetime(2026, 8, day, h, m)


def test_digest_never_fires_before_6am():
    for hour in (0, 3, 5):
        assert conveyor_notify.should_emit_daily_digest(T(hour), None) is False
        assert conveyor_notify.should_emit_daily_digest(
            T(hour), "2026-08-13") is False


def test_digest_fires_at_first_cycle_after_6am_once():
    assert conveyor_notify.should_emit_daily_digest(T(6, 0), "2026-08-13") is True
    # after emitting, guard holds for the rest of the day
    assert conveyor_notify.should_emit_daily_digest(T(6, 15), "2026-08-14") is False
    assert conveyor_notify.should_emit_daily_digest(T(23, 59), "2026-08-14") is False
    # next morning it fires again for the new prior day
    assert conveyor_notify.should_emit_daily_digest(
        T(6, 5, day=16), "2026-08-14") is True


def test_digest_day_is_prior_local_day():
    assert conveyor_notify.digest_day(T(6)) == "2026-08-14"


def test_emit_daily_digest_first_run_baselines_without_event(tmp_path):
    state = {}
    calls = []
    res = conveyor_notify.emit_daily_digest(
        state, now=T(7), dispatcher=lambda *a, **k: calls.append((a, k)),
        state_path=str(tmp_path / "s.json"))
    assert res is None and calls == []
    assert state["daily_digest_emitted_for"] == "2026-08-14"


def test_emit_daily_digest_once_with_prior_day_stats(tmp_path):
    state = {"daily_stats": {"2026-08-14": {
        "cycles": 3, "receipts": 2, "candidates": 5, "chain_failures": 1,
        "failure_reasons": ["stage axle_verify failed (rc=1)"],
        "registry_hops_ok": 1, "registry_hops_stopped": 0,
        "paperclip_issues": 2, "lovable_drafts": 1, "approval_cards": 1,
        "proved_first": 11126, "proved_last": 11130,
    }}}
    calls = []

    def dispatcher(subject, body, kind=None):
        calls.append((subject, body, kind))
        return {"receipt_id": "aristotle_notice_x", "email": "disabled"}

    res = conveyor_notify.emit_daily_digest(
        state, now=T(6, 10), dispatcher=dispatcher,
        state_path=str(tmp_path / "s.json"))
    assert res == {"receipt_id": "aristotle_notice_x", "email": "disabled"}
    assert len(calls) == 1
    subject, body, kind = calls[0]
    assert kind == "conveyor_daily_digest"
    assert "2026-08-14" in subject
    assert "11126 -> 11130 (delta +4)" in body
    assert "5 candidate(s)" in body
    assert "chain failures: 1" in body
    assert "SOLVER_NOTIFY_EMAIL=1" in body  # email posture stated, default OFF
    # second cycle the same morning: guard blocks a duplicate
    assert conveyor_notify.emit_daily_digest(
        state, now=T(6, 25), dispatcher=dispatcher,
        state_path=str(tmp_path / "s.json")) is None
    assert len(calls) == 1


def _day_stats(**over):
    s = {"cycles": 1, "receipts": 1, "candidates": 1, "chain_failures": 0,
         "failure_reasons": [], "registry_hops_ok": 0,
         "registry_hops_stopped": 0, "paperclip_issues": 0,
         "lovable_drafts": 0, "approval_cards": 0,
         "proved_first": 100, "proved_last": 100}
    s.update(over)
    return s


def test_digest_catches_up_missed_days_with_observed_stats(tmp_path):
    """Machine down across a 6am window: last digest covered Aug 18; Aug 19
    accumulated real stats but its window was missed; first cycle back is
    Aug 21 09:00 (digest_day = Aug 20, no stats). BOTH days must be digested:
    Aug 19 with its real numbers, Aug 20 honestly as 'no cycles observed'."""
    state = {
        "daily_digest_emitted_for": "2026-08-18",
        "daily_stats": {"2026-08-19": _day_stats(receipts=3, candidates=7)},
    }
    calls = []

    def dispatcher(subject, body, kind=None):
        calls.append((subject, body, kind))
        return {"receipt_id": f"n{len(calls)}", "email": "disabled"}

    res = conveyor_notify.emit_daily_digest(
        state, now=T(9, day=21), dispatcher=dispatcher,
        state_path=str(tmp_path / "s.json"))
    assert res == {"receipt_id": "n2", "email": "disabled"}
    assert len(calls) == 2
    assert "2026-08-19" in calls[0][0] and "7 candidate(s)" in calls[0][1]
    assert "2026-08-20" in calls[1][0]
    assert "No conveyor cycles were observed" in calls[1][1]
    assert state["daily_digest_emitted_for"] == "2026-08-20"
    # same morning again: everything is covered, nothing re-emits
    assert conveyor_notify.emit_daily_digest(
        state, now=T(9, 30, day=21), dispatcher=dispatcher,
        state_path=str(tmp_path / "s.json")) is None
    assert len(calls) == 2


def test_digest_catchup_skips_statless_gap_days(tmp_path):
    """Gap days with NO observed stats are skipped silently (nothing to
    report is not 'no cycles observed' x N spam); only digest_day itself
    always emits."""
    state = {"daily_digest_emitted_for": "2026-08-15",
             "daily_stats": {"2026-08-19": _day_stats()}}
    calls = []
    conveyor_notify.emit_daily_digest(
        state, now=T(7, day=21),
        dispatcher=lambda s, b, kind=None: calls.append(s) or {"ok": 1},
        state_path=str(tmp_path / "s.json"))
    # 16th/17th/18th had no stats -> skipped; 19th has stats; 20th = digest day
    assert len(calls) == 2
    assert "2026-08-19" in calls[0] and "2026-08-20" in calls[1]


def test_missed_digest_days_bad_guard_value_is_safe():
    assert conveyor_notify._missed_digest_days(
        "not-a-date", "2026-08-20", {"2026-08-19": {}}) == []
    assert conveyor_notify._missed_digest_days(
        None, "2026-08-20", {"2026-08-19": {}}) == []


def test_digest_with_no_stats_admits_nothing_happened():
    subject, body = conveyor_notify.build_daily_digest(None, "2026-08-14")
    assert "No conveyor cycles were observed" in body
    assert "No work is claimed" in body


# ---------------------------------------------------------------- daily stats

def test_accumulate_daily_stats_counts_observed_cycles_only():
    state = {}
    cycle1 = {"new_receipts": 2, "candidates": [{"name": "a"}, {"name": "b"}],
              "stopped_reason": None,
              "registry_hop": {"ran": True, "ok": True},
              "paperclip_issues_filed": 2, "lovable_drafts_queued": 1,
              "approval_cards_posted": 1}
    s = conveyor_notify.accumulate_daily_stats(
        state, cycle1, 11126, now=T(9))
    cycle2 = {"new_receipts": 0, "candidates": [],
              "stopped_reason": "stage cross_check failed (rc=2)",
              "registry_hop": {"ran": False},
              "paperclip_issues_filed": 0}
    s = conveyor_notify.accumulate_daily_stats(
        state, cycle2, 11130, now=T(10))
    assert s["cycles"] == 2
    assert s["receipts"] == 2 and s["candidates"] == 2
    assert s["chain_failures"] == 1
    assert s["failure_reasons"] == ["stage cross_check failed (rc=2)"]
    assert s["registry_hops_ok"] == 1 and s["registry_hops_stopped"] == 0
    assert s["paperclip_issues"] == 2
    assert s["lovable_drafts"] == 1 and s["approval_cards"] == 1
    assert s["proved_first"] == 11126 and s["proved_last"] == 11130


def test_accumulate_daily_stats_counts_flushed_cards_too():
    """Cards queued during a :18820 outage and delivered later via
    flush_pending_approval_cards are posted cards — the digest's 'Today
    approval cards posted' must include them, not undercount."""
    state = {}
    cycle = {"new_receipts": 0, "candidates": [],
             "registry_hop": {"ran": False},
             "approval_cards_posted": 1, "approval_cards_flushed": 2}
    s = conveyor_notify.accumulate_daily_stats(state, cycle, 100, now=T(9))
    assert s["approval_cards"] == 3


def test_accumulate_daily_stats_prunes_old_days():
    state = {}
    for day in range(1, 12):
        conveyor_notify.accumulate_daily_stats(
            state, {"new_receipts": 0, "candidates": [],
                    "registry_hop": {"ran": False}}, 1, now=T(9, day=day))
    assert len(state["daily_stats"]) == conveyor_notify.DAILY_STATS_KEEP
    assert "2026-08-01" not in state["daily_stats"]
    assert "2026-08-11" in state["daily_stats"]


def test_unreadable_registry_leaves_proved_delta_unknown():
    state = {}
    conveyor_notify.accumulate_daily_stats(
        state, {"new_receipts": 0, "candidates": [],
                "registry_hop": {"ran": False}}, None, now=T(9))
    day = "2026-08-15"
    subject, body = conveyor_notify.build_daily_digest(
        state["daily_stats"][day], day)
    assert "registry PROVED delta: unknown" in body
