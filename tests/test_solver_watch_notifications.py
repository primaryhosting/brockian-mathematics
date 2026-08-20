import json
from unittest.mock import patch

import pytest

from aristotle import solver_watch


def _events(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def test_dispatch_stages_locally_and_never_opens_url_when_email_disabled(
    tmp_path, monkeypatch
):
    outbox = tmp_path / "outbox.jsonl"
    monkeypatch.setattr(solver_watch, "OUTBOX", str(outbox))
    monkeypatch.setattr(solver_watch, "LOG", str(tmp_path / "watch.log"))
    monkeypatch.setattr(solver_watch, "EMAIL_ENABLED", False)

    with patch.object(
        solver_watch.urllib.request,
        "urlopen",
        side_effect=AssertionError("disabled notification path contacted Gmail"),
    ) as urlopen:
        result = solver_watch.dispatch_notification("subject", "body")

    assert result["email"] == "disabled"
    assert urlopen.call_count == 0
    events = _events(outbox)
    assert len(events) == 1
    assert events[0]["event"] == "notification.staged"
    assert events[0]["channel"] == "local_outbox"
    assert events[0]["receipt_id"] == result["receipt_id"]


def test_local_stage_is_idempotent(tmp_path, monkeypatch):
    outbox = tmp_path / "outbox.jsonl"
    monkeypatch.setattr(solver_watch, "OUTBOX", str(outbox))
    monkeypatch.setattr(solver_watch, "LOG", str(tmp_path / "watch.log"))

    first = solver_watch.stage_notification("same", "same")
    second = solver_watch.stage_notification("same", "same")

    assert first == second
    assert len(_events(outbox)) == 1


def test_send_email_itself_fails_closed_without_opt_in(tmp_path, monkeypatch):
    monkeypatch.setattr(solver_watch, "LOG", str(tmp_path / "watch.log"))
    monkeypatch.setattr(solver_watch, "EMAIL_ENABLED", False)

    with patch.object(
        solver_watch.urllib.request,
        "urlopen",
        side_effect=AssertionError("send_email bypassed its opt-in gate"),
    ) as urlopen:
        assert solver_watch.send_email("subject", "body") is False

    assert urlopen.call_count == 0


def test_explicit_opt_in_records_successful_email_delivery(tmp_path, monkeypatch):
    outbox = tmp_path / "outbox.jsonl"
    monkeypatch.setattr(solver_watch, "OUTBOX", str(outbox))
    monkeypatch.setattr(solver_watch, "LOG", str(tmp_path / "watch.log"))
    monkeypatch.setattr(solver_watch, "EMAIL_ENABLED", True)
    monkeypatch.setattr(solver_watch, "NOTIFY_TO", "reviewer@example.invalid")

    class Response:
        def __enter__(self):
            return self

        def __exit__(self, *_args):
            return False

        def read(self):
            return b"ok"

    with patch.object(
        solver_watch.urllib.request, "urlopen", return_value=Response()
    ) as urlopen:
        result = solver_watch.dispatch_notification("subject", "body")

    assert result["email"] == "succeeded"
    assert urlopen.call_count == 1
    events = _events(outbox)
    assert [event["event"] for event in events] == [
        "notification.staged",
        "notification.email_delivery",
    ]
    assert events[1]["status"] == "succeeded"
    assert events[1]["receipt_id"] == events[0]["receipt_id"]


def test_successful_delivery_receipt_prevents_duplicate_email(tmp_path, monkeypatch):
    outbox = tmp_path / "outbox.jsonl"
    monkeypatch.setattr(solver_watch, "OUTBOX", str(outbox))
    monkeypatch.setattr(solver_watch, "LOG", str(tmp_path / "watch.log"))
    monkeypatch.setattr(solver_watch, "EMAIL_ENABLED", True)
    monkeypatch.setattr(solver_watch, "send_email", lambda *_args: True)

    assert solver_watch.dispatch_notification("subject", "body")["email"] == "succeeded"
    with patch.object(solver_watch, "send_email") as send_email:
        result = solver_watch.dispatch_notification("subject", "body")

    assert result["email"] == "already_succeeded"
    assert send_email.call_count == 0
    assert len(_events(outbox)) == 2


def test_outbox_failure_leaves_running_state_for_safe_retry(tmp_path, monkeypatch):
    state = tmp_path / "state.json"
    state.write_text(json.dumps({
        "project-1": {
            "account": "admin",
            "name": "Target",
            "status": "RUNNING",
            "notified": False,
            "verdict": None,
        }
    }))
    monkeypatch.setattr(solver_watch, "STATE", str(state))
    monkeypatch.setattr(solver_watch, "MANIFEST", str(tmp_path / "manifest.json"))
    monkeypatch.setattr(solver_watch, "LOG", str(tmp_path / "watch.log"))
    monkeypatch.setattr(solver_watch, "ACCOUNTS", [("admin", "test-key")])
    monkeypatch.setattr(solver_watch, "list_projects", lambda _key: [{
        "id": "project-1",
        "created": "now",
        "name": "Target",
        "status": "IDLE",
    }])
    monkeypatch.setattr(
        solver_watch,
        "verdict_for",
        lambda _pid, _key: ("CANDIDATE", {"theorems": 1, "sorries": 0}),
    )
    monkeypatch.setattr(solver_watch, "_push_fleet_snapshot", lambda: None)
    monkeypatch.setattr(
        solver_watch,
        "dispatch_notification",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(OSError("outbox full")),
    )

    with pytest.raises(OSError, match="outbox full"):
        solver_watch.main()

    persisted = json.loads(state.read_text())
    assert persisted["project-1"]["status"] == "RUNNING"
    assert persisted["project-1"]["notified"] is False
