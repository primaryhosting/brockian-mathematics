"""Spend-attribution hop: conveyor → Paperclip RIE issues.

The Paperclip create endpoint has NO server-side dedupe (probed 2026-08-18:
client-supplied originKind/originFingerprint are ignored — the created issue
came back originKind="manual", originFingerprint="default"). Idempotency is
therefore entirely client-side: state["paperclip_issues"] keyed by receipt_id,
and state["proof_attempt_requests"] keyed by ISO week. These tests pin that
guard: re-running a cycle over the same outbox NEVER duplicates an issue.
"""
import datetime
import json

from unittest.mock import patch

import pytest

from aristotle import conveyor


@pytest.fixture(autouse=True)
def _isolated_log(tmp_path, monkeypatch):
    """Never write fake RIE identifiers into the real aristotle/conveyor.log."""
    monkeypatch.setattr(conveyor, "LOG", str(tmp_path / "conveyor.test.log"))


BODY = (
    "2 Aristotle projects completed in this poll.\n"
    "\U0001f9ea CANDIDATE [admin] arsub_j7c_r59_\n"
    "  86d11b35-23d0-4070-95cf-25bbf1015428\n"
    "\U0001f9ea CANDIDATE [chris] arsub_ozdg5si3\n"
    "  5326db72-7efe-4900-8afd-aac05d975a9f"
)


def _ev(rid, body=BODY):
    return {"schema": "acutis.aristotle.notification.v1",
            "event": "notification.staged", "receipt_id": rid,
            "kind": "solver_completion_digest", "body": body,
            "channel": "local_outbox"}


class FakePoster:
    """Counts POSTs; returns a fresh fake issue each call (or None if down)."""

    def __init__(self, up=True):
        self.up = up
        self.calls = []

    def __call__(self, payload, **kw):
        self.calls.append(payload)
        if not self.up:
            return None
        n = len(self.calls)
        return {"id": f"issue-{n}", "identifier": f"RIE-{900 + n}"}


# ------------------------------------------------------------- payload shape

def test_title_single_and_multi_candidate():
    one = [{"account": "admin", "name": "arsub_solo", "uuid": None}]
    assert conveyor.paperclip_issue_title(one) == \
        "Aristotle: arsub_solo — candidate ready"
    two = conveyor.parse_candidates(BODY)
    t = conveyor.paperclip_issue_title(two)
    assert t.startswith("Aristotle: arsub_j7c_r59_ (+1 more)")
    assert t.endswith("— candidate ready")


def test_issue_body_contains_candidates_verdict_links_and_receipt():
    ev = _ev("aristotle_notice_xyz")
    payload = conveyor.build_paperclip_issue(ev, conveyor.parse_candidates(BODY))
    body = payload["description"]
    assert "aristotle_notice_xyz" in body                       # idempotency key
    assert "86d11b35-23d0-4070-95cf-25bbf1015428" in body       # candidate uuid
    assert "arsub_ozdg5si3" in body
    assert "axle_verify.json" in body                           # verdict links
    assert "solver_state.json" in body
    assert "NOT registry-PROVED" in body                        # never overclaim
    assert "NOETHER" in body                                    # do-not-assign


# --------------------------------------------------------- batch idempotency

def test_one_issue_per_batch_and_rerun_never_duplicates():
    state = {}
    digests = [_ev("r1"), _ev("r2")]
    poster = FakePoster()
    assert conveyor.post_attribution_issues(state, digests, poster) == 2
    assert len(poster.calls) == 2  # exactly one POST per batch

    # SAME digests again (cursor not advanced / cycle re-run): zero POSTs
    again = FakePoster()
    assert conveyor.post_attribution_issues(state, digests, again) == 0
    assert again.calls == []
    assert set(state["paperclip_issues"]) == {"r1", "r2"}
    assert state["paperclip_issues"]["r1"]["identifier"] == "RIE-901"


def test_failed_post_queues_pending_and_flush_delivers_exactly_once():
    state = {}
    down = FakePoster(up=False)
    assert conveyor.post_attribution_issues(state, [_ev("r1")], down) == 0
    assert "r1" not in state["paperclip_issues"]
    assert [p["receipt_id"] for p in state["pending_paperclip"]] == ["r1"]

    # still down: re-seeing the same digest does NOT double-queue
    assert conveyor.post_attribution_issues(state, [_ev("r1")], down) == 0
    assert len(state["pending_paperclip"]) == 1

    # service back: flush delivers it once, and only once
    up = FakePoster()
    assert conveyor.flush_pending_paperclip(state, up) == 1
    assert state["paperclip_issues"]["r1"]["issue_id"] == "issue-1"
    assert state["pending_paperclip"] == []
    assert conveyor.flush_pending_paperclip(state, up) == 0
    assert len(up.calls) == 1


def test_flush_drops_pending_already_filed_elsewhere():
    state = {"paperclip_issues": {"r1": {"issue_id": "x"}},
             "pending_paperclip": [{"receipt_id": "r1", "payload": {"title": "t"}}]}
    up = FakePoster()
    assert conveyor.flush_pending_paperclip(state, up) == 0
    assert up.calls == []  # guard checked BEFORE any POST — no duplicate
    assert state["pending_paperclip"] == []


def test_digest_without_candidates_files_no_issue_but_is_recorded():
    state = {}
    poster = FakePoster()
    ev = _ev("r_empty", body="1 project completed.\n⏹️ STOPPED [admin] arsub_x\n")
    assert conveyor.post_attribution_issues(state, [ev], poster) == 0
    assert poster.calls == []
    # recorded as skipped so it is never re-examined
    assert state["paperclip_issues"]["r_empty"]["skipped"] == "no candidates"
    assert conveyor.post_attribution_issues(state, [ev], poster) == 0


def test_partial_failure_only_retries_the_failed_receipt():
    state = {}

    def flaky(payload, **kw):
        # r1's batch succeeds, r2's fails (poster sees title-distinct payloads)
        if "arsub_j7c_r59_" in payload["description"]:
            return {"id": "ok-1", "identifier": "RIE-950"}
        return None

    body2 = "\U0001f9ea CANDIDATE [admin] arsub_other\n  " \
            "11111111-2222-3333-4444-555555555555\n"
    assert conveyor.post_attribution_issues(
        state, [_ev("r1"), _ev("r2", body=body2)], flaky) == 1
    assert "r1" in state["paperclip_issues"]
    assert "r2" not in state["paperclip_issues"]
    assert [p["receipt_id"] for p in state["pending_paperclip"]] == ["r2"]

    # re-seeing both digests posts nothing (r1 filed, r2 queued) …
    retry = FakePoster()
    assert conveyor.post_attribution_issues(
        state, [_ev("r1"), _ev("r2", body=body2)], retry) == 0
    assert retry.calls == []
    # … and the flush delivers ONLY r2
    assert conveyor.flush_pending_paperclip(state, retry) == 1
    assert len(retry.calls) == 1
    assert "arsub_other" in retry.calls[0]["description"]


# ------------------------------------- per-POST durability (hard-kill window)

class KillAfterFirst:
    """Succeeds on the first POST, then simulates a hard kill mid-batch."""

    def __init__(self):
        self.calls = []

    def __call__(self, payload, **kw):
        self.calls.append(payload)
        if len(self.calls) > 1:
            raise RuntimeError("simulated hard kill mid-batch")
        return {"id": "issue-1", "identifier": "RIE-901"}


def test_batch_guard_hits_disk_after_each_post(tmp_path):
    """A hard kill between a successful POST and end-of-batch must NOT re-post
    the already-created issues next cycle: state_path is dumped per-POST."""
    sp = str(tmp_path / "state.json")
    state = {}
    with pytest.raises(RuntimeError):
        conveyor.post_attribution_issues(
            state, [_ev("r1"), _ev("r2")], KillAfterFirst(), state_path=sp)
    on_disk = json.loads((tmp_path / "state.json").read_text())
    assert on_disk["paperclip_issues"]["r1"]["identifier"] == "RIE-901"

    # "reboot": reload from disk — only the un-filed receipt is posted
    resumed = FakePoster()
    assert conveyor.post_attribution_issues(
        on_disk, [_ev("r1"), _ev("r2")], resumed, state_path=sp) == 1
    assert len(resumed.calls) == 1
    assert "r2" in resumed.calls[0]["description"]


def test_flush_guard_hits_disk_after_each_post(tmp_path):
    sp = str(tmp_path / "state.json")
    state = {"pending_paperclip": [
        {"receipt_id": "r1", "payload": {"title": "t1", "description": "d1"}},
        {"receipt_id": "r2", "payload": {"title": "t2", "description": "d2"}},
    ]}
    with pytest.raises(RuntimeError):
        conveyor.flush_pending_paperclip(state, KillAfterFirst(), state_path=sp)
    on_disk = json.loads((tmp_path / "state.json").read_text())
    assert "r1" in on_disk["paperclip_issues"]

    # reload: the stale delivered item still in pending is dropped by the
    # guard; only r2 is posted
    resumed = FakePoster()
    assert conveyor.flush_pending_paperclip(on_disk, resumed, state_path=sp) == 1
    assert len(resumed.calls) == 1
    assert resumed.calls[0]["title"] == "t2"
    assert on_disk["pending_paperclip"] == []


def test_weekly_guard_hits_disk_immediately(tmp_path):
    sp = str(tmp_path / "state.json")
    now = datetime.datetime(2026, 8, 18, tzinfo=datetime.UTC)  # 2026-W34
    assert conveyor.maybe_post_proof_attempt_request(
        {}, FakePoster(), now, state_path=sp) is True
    on_disk = json.loads((tmp_path / "state.json").read_text())
    assert "2026-W34" in on_disk["proof_attempt_requests"]


def test_no_state_path_writes_no_file(tmp_path, monkeypatch):
    """Pure-guard unit calls (state_path omitted) never touch the real state
    file, even if conveyor.STATE points somewhere real."""
    monkeypatch.setattr(conveyor, "STATE", str(tmp_path / "real_state.json"))
    conveyor.post_attribution_issues({}, [_ev("r1")], FakePoster())
    assert not (tmp_path / "real_state.json").exists()


# ------------------------------------------------------- pending-queue cap

def test_pending_trim_over_cap_is_loud(tmp_path):
    """Trimming the retry queue permanently drops attributions (the cursor is
    already past their receipts) — it must log, never drop silently."""
    n_over = 3
    pending = [{"receipt_id": f"r{i}", "payload": {"title": f"t{i}"}}
               for i in range(conveyor.PENDING_PAPERCLIP_KEEP + n_over)]
    state = {"pending_paperclip": pending}
    down = FakePoster(up=False)
    assert conveyor.flush_pending_paperclip(state, down) == 0
    assert len(state["pending_paperclip"]) == conveyor.PENDING_PAPERCLIP_KEEP
    # oldest were dropped, newest kept
    assert state["pending_paperclip"][0]["receipt_id"] == f"r{n_over}"
    logged = open(conveyor.LOG, encoding="utf-8").read()
    assert "PERMANENTLY dropping 3" in logged
    assert "'r0'" in logged and "'r2'" in logged


def test_cap_covers_the_real_142_receipt_backlog():
    """The live first run queued 142 receipts while :3101 was down; the cap
    must hold at least that with headroom."""
    assert conveyor.PENDING_PAPERCLIP_KEEP >= 142 * 2


# ------------------------------------------------- weekly proof-attempt issue

def test_weekly_proof_attempt_filed_once_per_iso_week():
    state = {}
    now = datetime.datetime(2026, 8, 18, tzinfo=datetime.UTC)  # 2026-W34
    p1 = FakePoster()
    assert conveyor.maybe_post_proof_attempt_request(state, p1, now) is True
    assert conveyor.maybe_post_proof_attempt_request(state, p1, now) is False
    assert len(p1.calls) == 1
    assert "2026-W34" in p1.calls[0]["title"]
    body = p1.calls[0]["description"]
    assert "/Users/acutis/Projects/brockian-mathematics" in body
    assert "lake build" in body
    assert "NOETHER" in body
    # next ISO week fires again
    nxt = now + datetime.timedelta(days=7)
    assert conveyor.maybe_post_proof_attempt_request(state, p1, nxt) is True
    assert set(state["proof_attempt_requests"]) == {"2026-W34", "2026-W35"}


def test_weekly_proof_attempt_failed_post_retries():
    state = {}
    now = datetime.datetime(2026, 8, 18, tzinfo=datetime.UTC)
    assert conveyor.maybe_post_proof_attempt_request(
        state, FakePoster(up=False), now) is False
    assert state["proof_attempt_requests"] == {}  # unrecorded → retried
    assert conveyor.maybe_post_proof_attempt_request(
        state, FakePoster(), now) is True


# ------------------------------------------------------ run_cycle integration

def _isolate(tmp_path, monkeypatch, events):
    outbox = tmp_path / "outbox.jsonl"
    with open(outbox, "w", encoding="utf-8") as fh:
        for ev in events:
            fh.write(json.dumps(ev, ensure_ascii=False) + "\n")
    attest = tmp_path / "attest"
    attest.mkdir(exist_ok=True)
    monkeypatch.setattr(conveyor, "OUTBOX", str(outbox))
    monkeypatch.setattr(conveyor, "CURSOR", str(tmp_path / "cursor.json"))
    monkeypatch.setattr(conveyor, "STATE", str(tmp_path / "state.json"))
    monkeypatch.setattr(conveyor, "LOG", str(tmp_path / "log"))
    monkeypatch.setattr(conveyor, "ATTEST_DIR", str(attest))
    (tmp_path / "cursor.json").write_text(json.dumps({
        "processed_receipt_ids": [],
        "attestation_fingerprint":
            conveyor.attestation_fingerprint(str(attest)),
    }))


def test_cycle_persists_issue_state_even_when_chain_fails(tmp_path, monkeypatch):
    """A failed chain keeps the CURSOR (receipts retried) but the paperclip
    guard in STATE survives — re-running the cycle never re-files the issue."""
    _isolate(tmp_path, monkeypatch, [_ev("r_chain_fail")])
    poster = FakePoster()
    monkeypatch.setattr(conveyor, "post_paperclip_issue", poster)
    fail = conveyor.StageResult(name="harvest_proofs", status="failed",
                                rc=1, seconds=0.1, tail="boom")
    with patch.object(conveyor, "run_chain", return_value=([fail], False)), \
         patch.object(conveyor.subprocess, "run") as prun, \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        prun.return_value.returncode = 1
        cycle = conveyor.run_cycle()

    assert cycle["paperclip_issues_filed"] == 1
    st = json.loads((tmp_path / "state.json").read_text())
    assert "r_chain_fail" in st["paperclip_issues"]
    # cursor NOT advanced (chain failed) — but the retry files nothing new
    cur = json.loads((tmp_path / "cursor.json").read_text())
    assert cur["processed_receipt_ids"] == []

    with patch.object(conveyor, "run_chain", return_value=([fail], False)), \
         patch.object(conveyor.subprocess, "run") as prun, \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        prun.return_value.returncode = 1
        cycle2 = conveyor.run_cycle()
    assert cycle2["paperclip_issues_filed"] == 0
    # exactly 1 batch POST total across both cycles (+1 weekly request)
    batch_posts = [p for p in poster.calls
                   if "candidate ready" in p["title"]]
    assert len(batch_posts) == 1


def test_cycle_with_paperclip_down_queues_then_delivers_exactly_once(
        tmp_path, monkeypatch):
    """Chain succeeds while :3101 is down → the cursor advances past the
    receipt, but the pending queue still carries the attribution: the next
    cycle delivers it exactly once, and later cycles never duplicate."""
    _isolate(tmp_path, monkeypatch, [_ev("r_pc_down")])
    down = FakePoster(up=False)
    monkeypatch.setattr(conveyor, "post_paperclip_issue", down)
    with patch.object(conveyor, "run_chain", return_value=([], True)), \
         patch.object(conveyor.subprocess, "run") as prun, \
         patch.object(conveyor, "post_lovable_queue", return_value=True):
        prun.return_value.returncode = 1
        cycle = conveyor.run_cycle()
    assert cycle["paperclip_issues_filed"] == 0
    st = json.loads((tmp_path / "state.json").read_text())
    assert [p["receipt_id"] for p in st["pending_paperclip"]] == ["r_pc_down"]
    cur = json.loads((tmp_path / "cursor.json").read_text())
    assert cur["processed_receipt_ids"] == ["r_pc_down"]  # cursor advanced

    # service back up: two more cycles → delivered exactly once total
    up = FakePoster()
    monkeypatch.setattr(conveyor, "post_paperclip_issue", up)
    for _ in range(2):
        with patch.object(conveyor, "run_chain", return_value=([], True)), \
             patch.object(conveyor.subprocess, "run") as prun, \
             patch.object(conveyor, "post_lovable_queue", return_value=True):
            prun.return_value.returncode = 1
            conveyor.run_cycle()
    batch_posts = [p for p in up.calls if "candidate ready" in p["title"]]
    assert len(batch_posts) == 1
    st = json.loads((tmp_path / "state.json").read_text())
    assert st["pending_paperclip"] == []
    assert "r_pc_down" in st["paperclip_issues"]
