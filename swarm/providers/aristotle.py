from __future__ import annotations

import json
import os
import subprocess
from dataclasses import dataclass
from typing import Any


@dataclass
class AristotleCLI:
    executable: str = "aristotle"

    def _run(self, *args: str) -> dict[str, Any]:
        proc = subprocess.run([self.executable, *args, "--json"], text=True,
                              capture_output=True, check=False)
        if proc.returncode:
            raise RuntimeError(proc.stderr.strip() or f"Aristotle exited {proc.returncode}")
        return json.loads(proc.stdout)

    def submit(self, prompt: str) -> str:
        if not os.environ.get("ARISTOTLE_API_KEY"):
            raise RuntimeError("ARISTOTLE_API_KEY is not configured")
        return str(self._run("submit", "--prompt", prompt)["id"])

    def poll(self, remote_id: str) -> dict[str, Any]:
        return self._run("status", remote_id)
