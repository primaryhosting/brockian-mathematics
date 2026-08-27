#!/usr/bin/env python3
"""render_dashboard.py — substitute dashboard_data.json into the template.

Usage: python3 aristotle/render_dashboard.py
Reads  aristotle/dashboard_template.html + aristotle/dashboard_data.json
Writes aristotle/dashboard.html (gitignored; publish as the Claude Artifact).
Fails loudly if the placeholder is missing or the data JSON is invalid.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PLACEHOLDER = "/*__DATA__*/"


def main() -> int:
    template = (HERE / "dashboard_template.html").read_text()
    if PLACEHOLDER not in template:
        print(f"FATAL: placeholder {PLACEHOLDER} not found in template", file=sys.stderr)
        return 1
    data_path = HERE / "dashboard_data.json"
    try:
        data = json.loads(data_path.read_text())
    except (OSError, json.JSONDecodeError) as e:
        print(f"FATAL: cannot load {data_path}: {e}", file=sys.stderr)
        return 1
    out = HERE / "dashboard.html"
    # </script> inside JSON strings would terminate the script block early.
    payload = json.dumps(data, separators=(",", ":")).replace("</", "<\\/")
    out.write_text(template.replace(PLACEHOLDER, payload, 1))
    print(f"wrote {out} ({out.stat().st_size:,} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
