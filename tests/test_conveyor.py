import json
import os
from unittest.mock import patch

import pytest

from aristotle import conveyor, conveyor_notify


@pytest.fixture(autouse=True)
def _no_real_paperclip(monkeypatch):
    """The spend-attribution hop must never reach the real Paperclip :3101
    from unit tests. Dedicated idempotency tests live in
    tests/test_conveyor_paperclip.py and inject their own posters."""
    monkeypatch.setattr(
        conveyor, "post_paperclip_issue",
        lambda payload, **kw: {"id": "test-issue-id", "identifier": "RIE-0"})


@pytest.fixture(autouse=True)
def _no_real_notify(monkeypatch):
    """The publish/notify legs must never reach the real ACUTIS :18820 or the
    solver outbox from run_cycle unit tests — a live server happily accepts
    real approval_gates rows (this bit once on 2026-08-18; four test-artifact
    cards landed in production). Dedicated leg tests live in
    tests/test_conveyor_notify.py and inject their own posters/probers/
    dispatchers."""
    monkeypatch.setattr(conveyor_notify, "post_approval_gate",
                        lambda payload, **kw: {"id": "test-gate-id"})
    monkeypatch.setattr(conveyor_notify, "gate_exists_serverside",
                        lambda rid, **kw: False)
    monkeypatch.setattr(conveyor_notify, "emit_daily_digest",
                        lambda state, **kw: None)


@pytest.fixture(autouse=True)
def _no_real_obsidian(monkeypatch):
    """The knowledge-graph leg must never reach the real Obsidian vault on
    /Volumes/BCC-Storage from run_cycle unit tests. Dedicated export tests
    (tmp vault) live in tests/test_export_obsidian.py."""
    monkeypatch.setattr(
        conveyor, "run_obsidian_export",
        lambda **kw: {"ran": False, "note": "mocked in unit tests"})


# Real outbox lines (verbatim shapes from aristotle/solver_notification_outbox.jsonl)
REAL_DIGEST_BODY = (
    "2 Aristotle projects completed in this poll.\n"
    "Proof candidates: 2 · stopped: 0\n"
    "Candidates are not registry-PROVED until local/AXLE verification passes.\n"
    "\n"
    "\U0001f9ea CANDIDATE [admin] arsub_j7c_r59_\n"
    "  86d11b35-23d0-4070-95cf-25bbf1015428\n"
    "\U0001f9ea CANDIDATE [chris] arsub_ozdg5si3\n"
    "  5326db72-7efe-4900-8afd-aac05d975a9f"
)


def _digest_event(rid, body=REAL_DIGEST_BODY, kind="solver_completion_digest"):
    return {
        "schema": "acutis.aristotle.notification.v1",
        "event": "notification.staged",
        "receipt_id": rid,
        "kind": kind,
        "subject": "[Aristotle] 2 completions — 2 candidates, 0 stopped",
        "body": body,
        "channel": "local_outbox",
    }


def _write_outbox(path, events):
    with open(path, "w", encoding="utf-8") as fh:
        for ev in events:
            fh.write(json.dumps(ev, sort_keys=True, ensure_ascii=False) + "\n")


# --------------------------------------------------------- candidate parsing

def test_parse_candidates_from_real_digest_body():
    cands = conveyor.parse_candidates(REAL_DIGEST_BODY)
    assert cands == [
        {"account": "admin", "name": "arsub_j7c_r59_",
         "uuid": "86d11b35-23d0-4070-95cf-25bbf1015428"},
        {"account": "chris", "name": "arsub_ozdg5si3",
         "uuid": "5326db72-7efe-4900-8afd-aac05d975a9f"},
    ]


def test_parse_candidates_ignores_stopped_and_handles_missing_uuid():
    body = (
        "3 Aristotle projects completed in this poll.\n"
        "\U0001f9ea CANDIDATE [admin] arsub_no_uuid\n"
        "⏹️ STOPPED [chris] arsub_gave_up\n"
        "  11111111-2222-3333-4444-555555555555\n"
    )
    cands = conveyor.parse_candidates(body)
    assert cands == [{"account": "admin", "name": "arsub_no_uuid", "uuid": None}]


def test_parse_candidates_empty_body():
    assert conveyor.parse_candidates("") == []
    assert conveyor.parse_candidates(None) == []


# --------------------------------------------------------- cursor idempotency

def test_new_digests_skips_processed_and_non_digest_events(tmp_path, monkeypatch):
    outbox = tmp_path / "outbox.jsonl"
    events = [
        _digest_event("aristotle_notice_aaa"),
        _digest_event("aristotle_notice_armed", kind="solver_watch_armed"),
        {"event": "notification.email_delivery",
         "receipt_id": "aristotle_notice_aaa", "status": "failed"},
        _digest_event("aristotle_notice_bbb"),
    ]
    _write_outbox(outbox, events)
    monkeypatch.setattr(conveyor, "OUTBOX", str(outbox))

    fresh = conveyor.new_digests(conveyor.read_outbox_events(), set())
    assert [e["receipt_id"] for e in fresh] == [
        "aristotle_notice_aaa", "aristotle_notice_bbb"]

    # after processing, the same outbox yields nothing (idempotent by receipt_id)
    done = {"aristotle_notice_aaa", "aristotle_notice_bbb"}
    assert conveyor.new_digests(conveyor.read_outbox_events(), done) == []


def test_new_digests_dedupes_repeated_receipt_ids(tmp_path, monkeypatch):
    outbox = tmp_path / "outbox.jsonl"
    _write_outbox(outbox, [_digest_event("aristotle_notice_dup"),
                           _digest_event("aristotle_notice_dup")])
    monkeypatch.setattr(conveyor, "OUTBOX", str(outbox))
    fresh = conveyor.new_digests(conveyor.read_outbox_events(), set())
    assert len(fresh) == 1


def test_cycle_advances_cursor_only_on_chain_success(tmp_path, monkeypatch):
    outbox = tmp_path / "outbox.jsonl"
    _write_outbox(outbox, [_digest_event("aristotle_notice_ccc")])
    cursor = tmp_path / "cursor.json"
    state = tmp_path / "state.json"
    # pre-existing cursor (not first run) with a baselined fingerprint
    cursor.write_text(json.dumps({
        "processed_receipt_ids": [],
        "attestation_fingerprint": conveyor.attestation_fingerprint(
            str(tmp_path / "no_attest")),
    }))
    monkeypatch.setattr(conveyor, "OUTBOX", str(outbox))
    monkeypatch.setattr(conveyor, "CURSOR", str(cursor))
    monkeypatch.setattr(conveyor, "STATE", str(state))
    monkeypatch.setattr(conveyor, "LOG", str(tmp_path / "log"))
    monkeypatch.setattr(conveyor, "ATTEST_DIR", str(tmp_path / "no_attest"))

    fail = conveyor.StageResult(name="harvest_proofs", status="failed",
                                rc=1, seconds=0.1, tail="boom")
    with patch.object(conveyor, "run_chain", return_value=([fail], False)), \
         patch.object(conveyor.subprocess, "run") as prun, \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        prun.return_value.returncode = 1  # pgrep: no verify_stage running
        cycle = conveyor.run_cycle()

    assert cycle["stopped_reason"].startswith("stage harvest_proofs failed")
    # cursor NOT advanced -> next cycle retries the same receipt
    cur = json.loads(cursor.read_text())
    assert cur["processed_receipt_ids"] == []

    with patch.object(conveyor, "run_chain", return_value=([], True)), \
         patch.object(conveyor.subprocess, "run") as prun, \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        prun.return_value.returncode = 1
        conveyor.run_cycle()
    cur = json.loads(cursor.read_text())
    assert cur["processed_receipt_ids"] == ["aristotle_notice_ccc"]


# --------------------------------------------------------- state atomicity

def test_atomic_json_dump_preserves_prior_file_on_failure(tmp_path):
    target = tmp_path / "state.json"
    conveyor._atomic_json_dump({"good": 1}, str(target))
    assert json.loads(target.read_text()) == {"good": 1}

    with pytest.raises(TypeError):
        conveyor._atomic_json_dump({"bad": object()}, str(target))
    # the prior good file is intact and still valid JSON
    assert json.loads(target.read_text()) == {"good": 1}


def test_atomic_json_dump_never_leaves_torn_target(tmp_path):
    target = tmp_path / "state.json"
    conveyor._atomic_json_dump({"v": 1}, str(target))
    with patch.object(conveyor.os, "replace",
                      side_effect=OSError("ENOSPC")), pytest.raises(OSError):
        conveyor._atomic_json_dump({"v": 2}, str(target))
    assert json.loads(target.read_text()) == {"v": 1}


# --------------------------------------------------------- chain gating

def _isolate(tmp_path, monkeypatch, events, cursor_obj=None):
    outbox = tmp_path / "outbox.jsonl"
    _write_outbox(outbox, events)
    cursor = tmp_path / "cursor.json"
    if cursor_obj is not None:
        cursor.write_text(json.dumps(cursor_obj))
    attest = tmp_path / "attest"
    attest.mkdir(exist_ok=True)
    monkeypatch.setattr(conveyor, "OUTBOX", str(outbox))
    monkeypatch.setattr(conveyor, "CURSOR", str(cursor))
    monkeypatch.setattr(conveyor, "STATE", str(tmp_path / "state.json"))
    monkeypatch.setattr(conveyor, "LOG", str(tmp_path / "log"))
    monkeypatch.setattr(conveyor, "ATTEST_DIR", str(attest))
    return attest


def test_no_new_candidates_never_invokes_heavy_chain(tmp_path, monkeypatch):
    attest = _isolate(tmp_path, monkeypatch, [])
    # cursor already baselined at the CURRENT fingerprint -> no registry hop
    (tmp_path / "cursor.json").write_text(json.dumps({
        "processed_receipt_ids": [],
        "attestation_fingerprint":
            conveyor.attestation_fingerprint(str(attest)),
    }))
    # make any real chain/hop use loud
    with patch.object(conveyor, "run_chain",
                      side_effect=AssertionError("chain must not run")), \
         patch.object(conveyor, "run_registry_hop",
                      side_effect=AssertionError("hop must not run")), \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        cycle = conveyor.run_cycle()
    assert cycle["new_receipts"] == 0
    assert cycle["stages"] == []


def test_new_candidates_invoke_chain_in_order_and_stop_on_failure():
    calls = []

    def runner(name, script, env_extra=None, timeout=None, timeout_fatal=True):
        calls.append(name)
        status = "failed" if name == "select_best" else "ok"
        return conveyor.StageResult(name=name, status=status,
                                    rc=0 if status == "ok" else 2,
                                    seconds=0.0, tail="")

    results, ok = conveyor.run_chain(runner=runner)
    assert not ok
    assert calls == ["harvest_proofs", "harvest_all", "verify_stage",
                     "select_best"]  # stops cleanly at the failed stage
    assert results[-1]["status"] == "failed"


def test_verify_stage_budget_exhaustion_is_nonfatal():
    def runner(name, script, env_extra=None, timeout=None, timeout_fatal=True):
        status = "budget_exhausted" if name == "verify_stage" else "ok"
        return conveyor.StageResult(name=name, status=status, rc=None,
                                    seconds=0.0, tail="")

    results, ok = conveyor.run_chain(runner=runner)
    assert ok
    assert [r["name"] for r in results] == [
        s[0] for s in conveyor.chain_stages()]


def test_chain_forces_auto_pr_live_off():
    stages = {name: env for name, _, env, _, _ in conveyor.chain_stages()}
    assert stages["auto_pr"]["AUTO_PR_LIVE"] == "0"


# --------------------------------------------------------- registry hop gating

def test_registry_hop_stops_on_strict_audit_failure():
    calls = []

    def runner(name, args, timeout=900):
        calls.append(name)
        status = "failed" if name == "audit_strict" else "ok"
        return conveyor.StageResult(name=name, status=status,
                                    rc=0 if status == "ok" else 1,
                                    seconds=0.0, tail="ERROR findings")

    results, ok, why = conveyor.run_registry_hop(runner=runner)
    assert not ok
    assert why == "audit_registry_consistency --strict failed"
    # audit failure = STOP: claims/observatory are never generated
    assert calls == ["gen_registry", "audit_strict"]


def test_registry_hop_full_pass():
    calls = []

    def runner(name, args, timeout=900):
        calls.append(name)
        return conveyor.StageResult(name=name, status="ok", rc=0,
                                    seconds=0.0, tail="")

    results, ok, why = conveyor.run_registry_hop(runner=runner)
    assert ok and why is None
    assert calls == ["gen_registry", "audit_strict", "gen_claims",
                     "gen_observatory"]


def test_first_run_baselines_fingerprint_without_registry_hop(
        tmp_path, monkeypatch):
    attest = _isolate(tmp_path, monkeypatch, [])
    (attest / "Mod.json").write_text('{"module": "Mod"}')
    with patch.object(conveyor, "run_registry_hop",
                      side_effect=AssertionError("hop must not run")), \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        cycle = conveyor.run_cycle()
    assert cycle["registry_hop"]["ran"] is False
    cur = json.loads((tmp_path / "cursor.json").read_text())
    assert cur["attestation_fingerprint"] == \
        conveyor.attestation_fingerprint(str(attest))


def test_changed_fingerprint_triggers_registry_hop(tmp_path, monkeypatch):
    attest = _isolate(tmp_path, monkeypatch, [],
                      cursor_obj={"processed_receipt_ids": [],
                                  "attestation_fingerprint": "stale"})
    (attest / "Mod.json").write_text('{"module": "Mod"}')
    hop = conveyor.StageResult(name="gen_registry", status="ok", rc=0,
                               seconds=0.0, tail="")
    with patch.object(conveyor, "run_registry_hop",
                      return_value=([hop], True, None)) as hop_mock, \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        cycle = conveyor.run_cycle()
    assert hop_mock.call_count == 1
    assert cycle["registry_hop"]["ran"] is True and cycle["registry_hop"]["ok"]
    cur = json.loads((tmp_path / "cursor.json").read_text())
    assert cur["attestation_fingerprint"] == \
        conveyor.attestation_fingerprint(str(attest))


def test_failed_registry_hop_keeps_stale_fingerprint_for_retry(
        tmp_path, monkeypatch):
    attest = _isolate(tmp_path, monkeypatch, [],
                      cursor_obj={"processed_receipt_ids": [],
                                  "attestation_fingerprint": "stale"})
    (attest / "Mod.json").write_text('{"module": "Mod"}')
    hop = conveyor.StageResult(name="audit_strict", status="failed", rc=1,
                               seconds=0.0, tail="")
    with patch.object(
            conveyor, "run_registry_hop",
            return_value=([hop], False,
                          "audit_registry_consistency --strict failed")), \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        cycle = conveyor.run_cycle()
    assert cycle["registry_hop"]["ok"] is False
    assert cycle["stopped_reason"] == \
        "audit_registry_consistency --strict failed"
    cur = json.loads((tmp_path / "cursor.json").read_text())
    assert cur["attestation_fingerprint"] == "stale"  # retried next cycle


# --------------------------------------------------------- lovable queueing

def test_lovable_down_queues_event_in_state(tmp_path, monkeypatch):
    monkeypatch.setattr(conveyor, "LOG", str(tmp_path / "log"))
    state = {}
    ok = conveyor.queue_or_send_lovable(
        state, "update", poster=lambda prompt: False)
    assert not ok
    assert len(state["pending_lovable_events"]) == 1
    assert state["pending_lovable_events"][0]["project"] == "spectral"

    delivered = conveyor.flush_pending_lovable(
        state, poster=lambda prompt: True)
    assert delivered == 1
    assert state["pending_lovable_events"] == []


def test_post_lovable_targets_queue_submit_only(monkeypatch):
    captured = {}

    class _Resp:
        def __enter__(self):
            return self

        def __exit__(self, *a):
            return False

        def read(self):
            return b"{}"

    def opener(req, timeout=None):
        captured["url"] = req.full_url
        captured["payload"] = json.loads(req.data.decode())
        return _Resp()

    assert conveyor.post_lovable_queue("hello", opener=opener)
    assert captured["url"].endswith("/queue-submit")
    assert captured["payload"] == {
        "items": [{"project": "spectral", "prompt": "hello"}]}


# --------------------------------------------------------- notify idempotency

def test_failed_chain_cycle_run_twice_never_notifies(tmp_path, monkeypatch):
    """A failed chain keeps the cursor, so every 15-min retry re-detects the
    same receipts. It must NOT queue a status card each time (the card would
    falsely claim the digests were processed). Reviewer bound: at most once;
    with completed-work gating the correct count is zero."""
    _isolate(tmp_path, monkeypatch, [_digest_event("aristotle_notice_fail")],
             cursor_obj={"processed_receipt_ids": [],
                         "attestation_fingerprint":
                             conveyor.attestation_fingerprint(
                                 str(tmp_path / "attest"))})
    fail = conveyor.StageResult(name="harvest_proofs", status="failed",
                                rc=1, seconds=0.1, tail="boom")
    with patch.object(conveyor, "run_chain",
                      return_value=([fail], False)), \
         patch.object(conveyor.subprocess, "run") as prun, \
         patch.object(conveyor, "post_lovable_queue",
                      return_value=True) as post:
        prun.return_value.returncode = 1  # pgrep: no verify_stage running
        conveyor.run_cycle()   # failed-chain cycle
        conveyor.run_cycle()   # 15 min later: same receipts, fails again
    assert post.call_count == 0


def test_deferred_chain_pgrep_guard_never_notifies(tmp_path, monkeypatch):
    """verify_stage already running -> chain deferred; no status card either."""
    _isolate(tmp_path, monkeypatch, [_digest_event("aristotle_notice_defer")],
             cursor_obj={"processed_receipt_ids": [],
                         "attestation_fingerprint":
                             conveyor.attestation_fingerprint(
                                 str(tmp_path / "attest"))})
    with patch.object(conveyor, "run_chain",
                      side_effect=AssertionError("chain must not run")), \
         patch.object(conveyor.subprocess, "run") as prun, \
         patch.object(conveyor, "post_lovable_queue",
                      return_value=True) as post:
        prun.return_value.returncode = 0  # pgrep: verify_stage IS running
        cycle = conveyor.run_cycle()
    assert cycle["stopped_reason"] == "verify_stage already running; deferred"
    assert post.call_count == 0


def test_repeating_failed_registry_hop_notifies_once(tmp_path, monkeypatch):
    """A registry hop failing the same way on the same attestations (stale
    fingerprint retained for retry) sends exactly one card, not one per
    15-min cycle — deduped by state['last_notified']."""
    attest = _isolate(tmp_path, monkeypatch, [],
                      cursor_obj={"processed_receipt_ids": [],
                                  "attestation_fingerprint": "stale"})
    (attest / "Mod.json").write_text('{"module": "Mod"}')
    hop = conveyor.StageResult(name="audit_strict", status="failed", rc=1,
                               seconds=0.0, tail="")
    with patch.object(
            conveyor, "run_registry_hop",
            return_value=([hop], False,
                          "audit_registry_consistency --strict failed")), \
         patch.object(conveyor, "post_lovable_queue",
                      return_value=True) as post:
        conveyor.run_cycle()
        conveyor.run_cycle()
    assert post.call_count == 1


def test_flushed_pending_events_persist_before_heavy_chain(
        tmp_path, monkeypatch):
    """Delivered pending events must be persisted immediately after the flush:
    the heavy chain can run for hours, and a crash before the end-of-cycle
    state dump must not resurrect already-delivered events (dup delivery)."""
    _isolate(tmp_path, monkeypatch, [_digest_event("aristotle_notice_crash")],
             cursor_obj={"processed_receipt_ids": [],
                         "attestation_fingerprint": "stale"})
    (tmp_path / "state.json").write_text(json.dumps({
        "pending_lovable_events": [
            {"queued_at": "2026-08-18T00:00:00+00:00",
             "project": "spectral", "prompt": "queued while :18793 was down"}],
    }))
    with patch.object(conveyor, "post_lovable_queue", return_value=True), \
         patch.object(conveyor.subprocess, "run") as prun, \
         patch.object(conveyor, "run_chain",
                      side_effect=RuntimeError("crash mid-chain")), \
         pytest.raises(RuntimeError):
        prun.return_value.returncode = 1  # pgrep: no verify_stage running
        conveyor.run_cycle()
    # the delivered event is already gone from the persisted state on disk
    persisted = json.loads((tmp_path / "state.json").read_text())
    assert persisted["pending_lovable_events"] == []
