from __future__ import annotations

import hashlib
import json
import os
import pathlib
import tempfile
from contextlib import contextmanager
from datetime import datetime, timezone
from typing import Any, Iterator

try:
    import fcntl
except ImportError:  # pragma: no cover
    fcntl = None


def canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


class EvidenceStore:
    """Append-only event log plus content-addressed immutable payloads."""

    def __init__(self, root: str | pathlib.Path):
        self.root = pathlib.Path(root)
        self.objects = self.root / "objects"
        self.events = self.root / "events.jsonl"
        self.lock = self.root / ".lock"

    def init(self) -> None:
        self.objects.mkdir(parents=True, exist_ok=True)
        self.lock.touch(exist_ok=True)

    @contextmanager
    def _locked(self) -> Iterator[None]:
        self.init()
        with self.lock.open("r+") as handle:
            if fcntl:
                fcntl.flock(handle, fcntl.LOCK_EX)
            try:
                yield
            finally:
                if fcntl:
                    fcntl.flock(handle, fcntl.LOCK_UN)

    def put(self, payload: Any) -> str:
        raw = canonical(payload)
        digest = hashlib.sha256(raw).hexdigest()
        path = self.objects / f"{digest}.json"
        with self._locked():
            if path.exists() and path.read_bytes() != raw:
                raise RuntimeError(f"content-address collision: {digest}")
            if not path.exists():
                fd, tmp = tempfile.mkstemp(dir=self.objects, prefix=".tmp-")
                try:
                    with os.fdopen(fd, "wb") as out:
                        out.write(raw)
                        out.flush()
                        os.fsync(out.fileno())
                    os.replace(tmp, path)
                finally:
                    if os.path.exists(tmp):
                        os.unlink(tmp)
        return digest

    def append(self, event: str, payload: Any) -> dict[str, Any]:
        ref = self.put(payload)
        record = {"at": datetime.now(timezone.utc).isoformat(), "event": event, "ref": ref}
        with self._locked():
            with self.events.open("ab") as out:
                out.write(canonical(record) + b"\n")
                out.flush()
                os.fsync(out.fileno())
        return record

    def get(self, digest: str) -> Any:
        raw = (self.objects / f"{digest}.json").read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise RuntimeError(f"tampered evidence object: {digest}")
        return json.loads(raw)

    def verify(self) -> list[str]:
        errors: list[str] = []
        if not self.events.exists():
            return errors
        for number, line in enumerate(self.events.read_bytes().splitlines(), 1):
            try:
                record = json.loads(line)
                self.get(record["ref"])
            except Exception as exc:  # noqa: BLE001
                errors.append(f"event {number}: {exc}")
        return errors
