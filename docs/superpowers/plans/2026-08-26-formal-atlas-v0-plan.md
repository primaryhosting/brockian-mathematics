# Formal Atlas v0 Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Ship Atlas v0 end-to-end: public `formal-atlas` pipeline repo with 3 harvesters (Brockian, Metamath, Mathlib), normalized schema, Wiedijk-100 concept seed, Supabase `atlas_*` tables, weekly editions, and the `/atlas` frontend on torus.riemannlab.com.

**Architecture:** Harvest → Align → Serve (approved spec: `docs/superpowers/specs/2026-08-26-formal-atlas-design.md`). Harvesters run on GitHub Actions (Mac Mini NOT in the loop), emit one normalized `statements.jsonl` + `manifest.json` each, upsert to Riemann Supabase via a shared loader, and attach editions to GitHub Releases. The Lovable site (`dd8308ac`) reads Supabase anon.

**Tech Stack:** Python 3.12 (stdlib + `requests`, `pyyaml`, `jsonschema`, `pytest`), GitHub Actions, Supabase (PostgREST), Lovable frontend via MCP prompts.

**Hard constraints (read first):**
- Local dev machine has ~2.6 GiB free disk. Tests use small pinned fixtures ONLY. Never download `set.mm` (51 MB) or mathlib declaration data (100+ MB) locally; full harvests run on Actions.
- Method/epistemics page: `docs/atlas/METHOD.md` in brockian-mathematics — the tier rules there are contract, not decoration. CANDIDATE never enters headline counts. All displayed numbers are harvester-measured.
- ⚠ `RIEMANN_SUPABASE_KEY` in the vault 401s as a service key. Migrations are applied via Lovable MCP `query_database`; the Actions secret is a HUMAN-GATED step (Task 12).
- The Brockian public authority is `https://torus.riemannlab.com/verified-registry.json` (schema `brockian-public-verified-registry/v1`, 11,819 entries, fields: `name, module, register, kind, statement, axioms, axioms_ok, axle_verdict, sorry_free, source, verified_by`). NEVER read `registry/theorems.json` for public display.

---

## File structure (new repo `~/Projects/formal-atlas` → GitHub `primaryhosting/formal-atlas`, public)

```
formal-atlas/
├── README.md                        # what/why, links to METHOD + spec, edition badge
├── DATA-LICENSES.md                 # per-library license notices (Task 2)
├── pyproject.toml                   # deps + pytest config
├── schema/
│   ├── statement.schema.json        # normalized statement record (Task 2)
│   └── manifest.schema.json         # harvester manifest (Task 2)
├── atlas/                           # shared package
│   ├── __init__.py
│   ├── emit.py                      # write/validate statements.jsonl + manifest.json (Task 3)
│   └── load.py                      # Supabase upsert loader (Task 10)
├── harvesters/
│   ├── brockian/harvest.py          # Task 4
│   ├── metamath/harvest.py          # Task 5
│   └── mathlib/harvest.py           # Task 6
├── concepts/
│   ├── wiedijk100.yaml              # concept seed + CURATED alignments (Task 8)
│   └── sync_concepts.py             # concepts yaml → Supabase rows (Task 10)
├── tools/
│   └── build_wiedijk_seed.py        # one-shot: mathlib docs/100.yaml → wiedijk100.yaml (Task 8)
├── migrations/
│   └── 001_atlas_tables.sql         # Task 9
├── tests/
│   ├── fixtures/
│   │   ├── brockian_registry_small.json
│   │   ├── set_mm_excerpt.mm
│   │   ├── mathlib_decls_small.json
│   │   └── mathlib_100_small.yaml
│   ├── test_emit.py
│   ├── test_brockian.py
│   ├── test_metamath.py
│   ├── test_mathlib.py
│   ├── test_wiedijk_seed.py
│   └── test_loader.py
└── .github/workflows/
    ├── ci.yml                       # pytest on push/PR (Task 7)
    ├── harvest.yml                  # scheduled matrix harvest + load (Task 11)
    └── edition.yml                  # weekly edition release (Task 11)
```

**Working directory for all tasks: `~/Projects/formal-atlas`.** Commit after every task (surgical `git add` of named files only — house rule: never `git add -A`).

---

## Chunk 1: Scaffold, schema, emit library

### Task 1: Repo scaffold

**Files:** Create: `README.md`, `pyproject.toml`, `.gitignore`, `atlas/__init__.py`

- [ ] **Step 1: Create repo + scaffold**

```bash
mkdir -p ~/Projects/formal-atlas && cd ~/Projects/formal-atlas
git init -b main
mkdir -p schema atlas harvesters/brockian harvesters/metamath harvesters/mathlib \
         concepts tools migrations tests/fixtures .github/workflows
touch atlas/__init__.py
```

- [ ] **Step 2: Write `pyproject.toml`**

```toml
[project]
name = "formal-atlas"
version = "0.0.1"
description = "Harvest pipeline for the Formal Atlas — a living map of machine-verified mathematics"
requires-python = ">=3.11"
dependencies = ["requests>=2.31", "pyyaml>=6.0", "jsonschema>=4.21"]

[project.optional-dependencies]
dev = ["pytest>=8.0"]

[tool.pytest.ini_options]
testpaths = ["tests"]
```

- [ ] **Step 3: Write `.gitignore`**

```
__pycache__/
*.pyc
.venv/
out/
*.jsonl
!tests/fixtures/*
```

- [ ] **Step 4: Write `README.md`** — title "The Formal Atlas — pipeline", one paragraph of mission (lift from spec §1), architecture diagram (lift from spec §3), links to: METHOD page (brockian-mathematics `docs/atlas/METHOD.md` GitHub URL), torus.riemannlab.com/atlas, the Mechanical Reproduction paper PDF (euler-sair-stage2 public repo), and a "Editions" section explaining weekly releases. State explicitly: "The atlas reports each library's own checked status; it never re-checks foreign proofs."

- [ ] **Step 5: Commit**

```bash
git add README.md pyproject.toml .gitignore atlas/__init__.py
git commit -m "scaffold: formal-atlas pipeline repo"
```

### Task 2: Normalized schemas + licenses doc

**Files:** Create: `schema/statement.schema.json`, `schema/manifest.schema.json`, `DATA-LICENSES.md`, Test: `tests/test_emit.py` (schema-validity part)

- [ ] **Step 1: Write `schema/statement.schema.json`**

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/primaryhosting/formal-atlas/schema/statement.schema.json",
  "title": "Atlas normalized statement",
  "type": "object",
  "required": ["library", "native_name", "kind", "source_url"],
  "additionalProperties": false,
  "properties": {
    "library":        {"type": "string", "enum": ["brockian", "metamath", "mathlib", "afp", "coq", "hollight", "mizar"]},
    "native_name":    {"type": "string", "minLength": 1},
    "kind":           {"type": "string", "enum": ["theorem", "definition", "axiom", "lemma", "corollary", "other"]},
    "statement_text": {"type": ["string", "null"]},
    "module":         {"type": ["string", "null"]},
    "source_url":     {"type": "string", "pattern": "^https://"},
    "subject_codes":  {"type": "array", "items": {"type": "string"}, "default": []}
  }
}
```

- [ ] **Step 2: Write `schema/manifest.schema.json`**

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/primaryhosting/formal-atlas/schema/manifest.schema.json",
  "title": "Atlas harvest manifest",
  "type": "object",
  "required": ["library", "harvester_version", "source_version", "statement_count", "harvested_at", "sha256"],
  "additionalProperties": false,
  "properties": {
    "library":           {"type": "string"},
    "harvester_version": {"type": "string"},
    "source_version":    {"type": "string", "description": "upstream commit/etag/date identifying what was harvested"},
    "statement_count":   {"type": "integer", "minimum": 0},
    "harvested_at":      {"type": "string", "format": "date-time"},
    "sha256":            {"type": "string", "description": "checksum of statements.jsonl"},
    "subject_derivation": {"type": ["string", "null"], "description": "how subject_codes were derived for this library"}
  }
}
```

- [ ] **Step 3: Write `DATA-LICENSES.md`** — table: Brockian registry (project-owned; cite repo LICENSE), Metamath `set.mm` (CC0), Mathlib (Apache-2.0); note "metadata-only harvesting: names, kinds, statement strings, links" and the AFP rule from spec §9 for later libraries.

- [ ] **Step 4: Commit**

```bash
git add schema/statement.schema.json schema/manifest.schema.json DATA-LICENSES.md
git commit -m "schema: normalized statement + manifest contracts, data licenses"
```

### Task 3: `atlas/emit.py` — the one writer every harvester uses

**Files:** Create: `atlas/emit.py`, Test: `tests/test_emit.py`

- [ ] **Step 1: Write the failing test `tests/test_emit.py`**

```python
import json, pathlib, pytest
from atlas.emit import write_harvest

def _stmt(name="Foo.bar"):
    return {"library": "brockian", "native_name": name, "kind": "theorem",
            "statement_text": "x = x", "module": "Foo", "subject_codes": [],
            "source_url": "https://torus.riemannlab.com/explore/lean-registry"}

def test_write_harvest_emits_jsonl_and_manifest(tmp_path):
    out = write_harvest(tmp_path, "brockian", [_stmt(), _stmt("Foo.baz")],
                        harvester_version="0.0.1", source_version="test-v1")
    lines = (tmp_path / "statements.jsonl").read_text().strip().split("\n")
    assert len(lines) == 2
    man = json.loads((tmp_path / "manifest.json").read_text())
    assert man["statement_count"] == 2
    assert man["library"] == "brockian"
    assert len(man["sha256"]) == 64

def test_write_harvest_rejects_invalid_statement(tmp_path):
    bad = _stmt(); del bad["source_url"]
    with pytest.raises(Exception):
        write_harvest(tmp_path, "brockian", [bad],
                      harvester_version="0.0.1", source_version="test-v1")

def test_write_harvest_rejects_duplicate_native_name(tmp_path):
    with pytest.raises(ValueError, match="duplicate"):
        write_harvest(tmp_path, "brockian", [_stmt(), _stmt()],
                      harvester_version="0.0.1", source_version="test-v1")
```

- [ ] **Step 2: Run to verify failure** — `cd ~/Projects/formal-atlas && python3 -m venv .venv && .venv/bin/pip install -e '.[dev]' -q && .venv/bin/pytest tests/test_emit.py -q` — Expected: FAIL (`ModuleNotFoundError` / `ImportError: write_harvest`).

- [ ] **Step 3: Write `atlas/emit.py`**

```python
"""Single writer for harvester output: validated statements.jsonl + manifest.json.

Every harvester calls write_harvest(); nothing else writes these files. Validation
here is the schema gate the spec's CI requires — a harvester emitting garbage
fails loudly at emit time, not at load time.
"""
import datetime as _dt
import hashlib
import json
import pathlib

import jsonschema

_SCHEMA_DIR = pathlib.Path(__file__).resolve().parent.parent / "schema"
_STMT_SCHEMA = json.loads((_SCHEMA_DIR / "statement.schema.json").read_text())
_MAN_SCHEMA = json.loads((_SCHEMA_DIR / "manifest.schema.json").read_text())


def write_harvest(out_dir, library, statements, *, harvester_version, source_version,
                  subject_derivation=None):
    out_dir = pathlib.Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    validator = jsonschema.Draft202012Validator(_STMT_SCHEMA)
    seen = set()
    lines = []
    for s in statements:
        validator.validate(s)
        if s["library"] != library:
            raise ValueError(f"statement library {s['library']!r} != harvest library {library!r}")
        if s["native_name"] in seen:
            raise ValueError(f"duplicate native_name: {s['native_name']}")
        seen.add(s["native_name"])
        lines.append(json.dumps(s, ensure_ascii=False, sort_keys=True))
    blob = ("\n".join(lines) + "\n") if lines else ""
    (out_dir / "statements.jsonl").write_text(blob, encoding="utf-8")
    manifest = {
        "library": library,
        "harvester_version": harvester_version,
        "source_version": source_version,
        "statement_count": len(lines),
        "harvested_at": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        "sha256": hashlib.sha256(blob.encode("utf-8")).hexdigest(),
        "subject_derivation": subject_derivation,
    }
    jsonschema.Draft202012Validator(_MAN_SCHEMA).validate(manifest)
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return manifest
```

- [ ] **Step 4: Run tests** — `.venv/bin/pytest tests/test_emit.py -q` — Expected: 3 passed.

- [ ] **Step 5: Commit**

```bash
git add atlas/emit.py tests/test_emit.py
git commit -m "emit: validated single-writer for harvest output"
```

## Chunk 2: The three v0 harvesters

Common harvester contract (spec §5): `python3 harvesters/<lib>/harvest.py --out out/<lib> [--source PATH_OR_URL]`. `--source` accepts a local fixture path in tests; defaults to the real upstream URL in production. Network access happens ONLY under `if __name__ == "__main__"` paths, never in unit-tested pure functions.

### Task 4: Brockian harvester

**Files:** Create: `harvesters/brockian/harvest.py`, `tests/fixtures/brockian_registry_small.json`, Test: `tests/test_brockian.py`

- [ ] **Step 1: Write fixture `tests/fixtures/brockian_registry_small.json`** — hand-write 5 entries copying the REAL registry shape exactly (schema key `brockian-public-verified-registry/v1`, `theorems` list with fields `name, module, register, kind, statement, axioms, axioms_ok, axle_verdict, sorry_free, source, verified_by`): **2** with `register="PROVED", axioms_ok=true, sorry_free=true` (these are the only two that qualify → the test's `statement_count == 2`); 1 with `register="CONDITIONAL"`; 1 PROVED but `sorry_free=false`; 1 PROVED but `axioms_ok=false`. Copy 2 real entries from `curl -s https://torus.riemannlab.com/verified-registry.json | python3 -c "import json,sys; d=json.load(sys.stdin); print(json.dumps(d['theorems'][:2], indent=1))"` and hand-edit the other 3 variants from them.

- [ ] **Step 2: Write the failing test `tests/test_brockian.py`**

```python
import json, pathlib
from harvesters.brockian.harvest import harvest

FIX = pathlib.Path(__file__).parent / "fixtures" / "brockian_registry_small.json"

def test_harvests_only_proved_sorry_free(tmp_path):
    man = harvest(source=str(FIX), out_dir=tmp_path)
    rows = [json.loads(l) for l in (tmp_path / "statements.jsonl").read_text().splitlines()]
    assert man["statement_count"] == 2          # 3 PROVED minus 1 with sorry_free=false... see fixture
    assert all(r["library"] == "brockian" for r in rows)
    assert all(r["source_url"].startswith("https://torus.riemannlab.com") for r in rows)

def test_module_becomes_module_and_kind_maps(tmp_path):
    harvest(source=str(FIX), out_dir=tmp_path)
    rows = [json.loads(l) for l in (tmp_path / "statements.jsonl").read_text().splitlines()]
    r = rows[0]
    assert r["module"] and r["kind"] in {"theorem", "definition", "lemma", "axiom", "other"}
```

(Adjust the expected count to match the fixture actually written in Step 1 — the invariant under test: only `register=="PROVED" and axioms_ok and sorry_free` rows are emitted.)

- [ ] **Step 3: Run to verify failure** — `.venv/bin/pytest tests/test_brockian.py -q` — Expected: FAIL (module not found).

- [ ] **Step 4: Write `harvesters/brockian/harvest.py`**

```python
"""Brockian harvester — reads ONLY the prover-owned sanitized public registry.

Inclusion rule (the library's own checked status, per METHOD.md): register PROVED,
axioms_ok, sorry_free. Everything else is not machine-verified mathematics and is
not the atlas's to report.
"""
import argparse
import json
import pathlib
import sys
import urllib.parse

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))
from atlas.emit import write_harvest

DEFAULT_SOURCE = "https://torus.riemannlab.com/verified-registry.json"
HARVESTER_VERSION = "0.1.0"
_KINDS = {"theorem": "theorem", "lemma": "lemma", "def": "definition",
          "definition": "definition", "axiom": "axiom"}


def _load(source):
    if source.startswith("http"):
        import requests
        r = requests.get(source, timeout=120)
        r.raise_for_status()
        return r.json()
    return json.loads(pathlib.Path(source).read_text())


def to_statement(entry):
    return {
        "library": "brockian",
        "native_name": entry["name"],
        "kind": _KINDS.get(str(entry.get("kind", "")).lower(), "other"),
        "statement_text": entry.get("statement") or None,
        "module": entry.get("module") or None,
        "source_url": "https://torus.riemannlab.com/explore/lean-registry?name="
                      + urllib.parse.quote(entry["name"]),
        "subject_codes": [],
    }


def harvest(source=DEFAULT_SOURCE, out_dir="out/brockian"):
    data = _load(source)
    if data.get("schema") != "brockian-public-verified-registry/v1":
        raise SystemExit(f"unexpected registry schema: {data.get('schema')!r}")
    rows = [to_statement(e) for e in data["theorems"]
            if e.get("register") == "PROVED" and e.get("axioms_ok") and e.get("sorry_free")]
    return write_harvest(out_dir, "brockian", rows,
                         harvester_version=HARVESTER_VERSION,
                         source_version=data.get("schema", "unknown"),
                         subject_derivation="module prefix (not yet mapped to MSC)")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", default=DEFAULT_SOURCE)
    ap.add_argument("--out", default="out/brockian")
    a = ap.parse_args()
    print(json.dumps(harvest(source=a.source, out_dir=a.out), indent=2))
```

- [ ] **Step 5: Run tests** — `.venv/bin/pytest tests/test_brockian.py -q` — Expected: pass. If the count assertion mismatches, fix the TEST to match the fixture (the filter rule is the contract).

- [ ] **Step 6: One live smoke (network, ~3 MB, allowed)** — `.venv/bin/python harvesters/brockian/harvest.py --out /tmp/atlas-smoke-brockian | python3 -c "import json,sys; m=json.load(sys.stdin); assert m['statement_count'] > 11000, m; print('live count:', m['statement_count'])"` — Expected: `live count: ~11500+`. Then `rm -rf /tmp/atlas-smoke-brockian`.

- [ ] **Step 7: Commit**

```bash
git add harvesters/brockian/harvest.py tests/test_brockian.py tests/fixtures/brockian_registry_small.json
git commit -m "harvester: brockian (sanitized registry, PROVED+axioms_ok+sorry_free only)"
```

### Task 5: Metamath harvester

**Files:** Create: `harvesters/metamath/harvest.py`, `tests/fixtures/set_mm_excerpt.mm`, Test: `tests/test_metamath.py`

- [ ] **Step 1: Write fixture `tests/fixtures/set_mm_excerpt.mm`** — a ~60-line hand-written excerpt in genuine set.mm syntax: one `$(` … `$)` section header comment (`#*#*#*` style header lines with a section title), two `$a` statements (one `ax-…` name, one `df-…` name), two `$p … $= … $.` theorems each preceded by a `$(` description comment `$)`, and one `$c`/`$v` line to be ignored. Example core lines:

```
$( #*#*#*#*#*#*#*#*#*#*#*#*#*#*
      Propositional calculus
   #*#*#*#*#*#*#*#*#*#*#*#*#* $)
$c ( ) -> wff $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
df-bi $a |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $.
$( Principle of identity. $)
id $p |- ( ph -> ph ) $= wph wph ax-1 $.
$( Modus ponens for biconditional. $)
mpbi $p |- ps $= wph wps ax-1 $.
```

- [ ] **Step 2: Write the failing test `tests/test_metamath.py`**

```python
import json, pathlib
from harvesters.metamath.harvest import parse_mm, harvest

FIX = pathlib.Path(__file__).parent / "fixtures" / "set_mm_excerpt.mm"

def test_parse_extracts_labels_kinds_sections():
    rows = list(parse_mm(FIX.read_text().splitlines()))
    by = {r["native_name"]: r for r in rows}
    assert by["id"]["kind"] == "theorem"
    assert by["ax-1"]["kind"] == "axiom"
    assert by["df-bi"]["kind"] == "definition"
    assert by["id"]["module"] == "Propositional calculus"
    assert "ph -> ph" in by["id"]["statement_text"]

def test_harvest_emits_valid_output(tmp_path):
    man = harvest(source=str(FIX), out_dir=tmp_path)
    assert man["library"] == "metamath"
    assert man["statement_count"] == 4  # 2 $a + 2 $p; $c/$v ignored
    rows = [json.loads(l) for l in (tmp_path / "statements.jsonl").read_text().splitlines()]
    assert all(r["source_url"] == f"https://us.metamath.org/mpeuni/{r['native_name']}.html" for r in rows)
```

- [ ] **Step 3: Run to verify failure** — Expected: FAIL (module not found).

- [ ] **Step 4: Write `harvesters/metamath/harvest.py`** — a line-streaming parser (set.mm is 51 MB; never hold parsed proofs). Rules:
  - Track current section: a comment block whose interior contains a line of `#*#*` marks — take the first non-decorative line inside it as the section title.
  - A statement is `LABEL $a MATH $.` or `LABEL $p MATH $= PROOF $.` — capture LABEL and MATH (text between `$a`/`$p` and `$=` or `$.`), skip everything else (`$c $v $d $f $e ${ $}`).
  - Kind: label starts with `ax-` → axiom; `df-` → definition; other `$a` → axiom; `$p` → theorem.
  - `statement_text` = the MATH string collapsed to single spaces; `module` = current section title; `source_url` = `https://us.metamath.org/mpeuni/<label>.html`.
  - `harvest(source, out_dir)`: source is a local path or URL; for URLs stream with `requests.get(stream=True)` and iterate lines without writing the file to disk.
  - `source_version`: for URLs use the response `ETag`/`Last-Modified` header (fall back to harvest date); for files use the file name.

```python
"""Metamath harvester — streams set.mm, emits $a/$p labels with section context."""
import argparse, json, pathlib, re, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))
from atlas.emit import write_harvest

DEFAULT_SOURCE = "https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm"
HARVESTER_VERSION = "0.1.0"
_STMT = re.compile(r"^\s*(\S+)\s+\$([ap])\s+(.*)$")


def parse_mm(lines):
    section = None
    in_comment = False
    comment_buf = []
    pending = None  # (label, kind_char, math_parts)
    for raw in lines:
        line = raw.rstrip("\n")
        # Statement match takes precedence over comment detection: a trailing
        # same-line comment (`foo $a x $. $( note $)`) must not swallow the
        # statement. Only a line that BEGINS a comment enters comment mode.
        if pending is None and line.lstrip().startswith("$(") :
            in_comment = True
            comment_buf = []
        if in_comment:
            comment_buf.append(line)
            if "$)" in line:
                in_comment = False
                block = "\n".join(comment_buf)
                if "#*#*" in block:
                    for cand in block.splitlines():
                        t = cand.strip().strip("$()").strip()
                        if t and "#*" not in t:
                            section = t
                            break
            continue
        if pending is not None:
            label, kc, parts = pending
            end = line.split("$=")[0].split("$.")[0]
            parts.append(end)
            if "$=" in line or "$." in line:
                yield _row(label, kc, " ".join(" ".join(parts).split()), section)
                pending = None
            continue
        m = _STMT.match(line)
        if m:
            label, kc, rest = m.group(1), m.group(2), m.group(3)
            head = rest.split("$=")[0].split("$.")[0]
            if "$=" in rest or "$." in rest:
                yield _row(label, kc, " ".join(head.split()), section)
            else:
                pending = (label, kc, [head])


def _row(label, kind_char, math, section):
    if kind_char == "p":
        kind = "theorem"
    elif label.startswith("ax-"):
        kind = "axiom"
    elif label.startswith("df-"):
        kind = "definition"
    else:
        kind = "axiom"
    return {"library": "metamath", "native_name": label, "kind": kind,
            "statement_text": math or None, "module": section,
            "source_url": f"https://us.metamath.org/mpeuni/{label}.html",
            "subject_codes": []}


def harvest(source=DEFAULT_SOURCE, out_dir="out/metamath"):
    if source.startswith("http"):
        import requests
        r = requests.get(source, stream=True, timeout=300)
        r.raise_for_status()
        rows = list(parse_mm(l.decode("utf-8", "replace") for l in r.iter_lines()))
        src_ver = r.headers.get("ETag") or r.headers.get("Last-Modified") or "unknown"
    else:
        rows = list(parse_mm(pathlib.Path(source).read_text().splitlines()))
        src_ver = pathlib.Path(source).name
    return write_harvest(out_dir, "metamath", rows,
                         harvester_version=HARVESTER_VERSION, source_version=src_ver,
                         subject_derivation="set.mm chapter headers")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", default=DEFAULT_SOURCE)
    ap.add_argument("--out", default="out/metamath")
    a = ap.parse_args()
    print(json.dumps(harvest(source=a.source, out_dir=a.out), indent=2))
```

- [ ] **Step 5: Run tests** — `.venv/bin/pytest tests/test_metamath.py -q` — Expected: pass. Iterate parser vs fixture until green (the fixture is the spec).
- [ ] **Step 6: Do NOT live-smoke locally** (51 MB; disk constraint). Live validation happens on Actions in Task 11.
- [ ] **Step 7: Commit** — `git add harvesters/metamath/harvest.py tests/test_metamath.py tests/fixtures/set_mm_excerpt.mm && git commit -m "harvester: metamath (streaming set.mm parser)"`

### Task 6: Mathlib harvester

**Files:** Create: `harvesters/mathlib/harvest.py`, `tests/fixtures/mathlib_decls_small.json`, Test: `tests/test_mathlib.py`

**Upstream probe first (do not guess the shape):**

- [ ] **Step 1: Probe the doc-gen4 export shape (headers + first KB only — no full download)**

```bash
curl -s --max-time 20 -r 0-2000 https://leanprover-community.github.io/mathlib4_docs/declarations/declaration-data.bmp | head -c 600
curl -sI --max-time 20 https://leanprover-community.github.io/mathlib4_docs/declarations/declaration-data.bmp | grep -iE "HTTP|content-length"
```

Record: the working URL (try `.bmp` then `.json` variants), whether the payload is a JSON object keyed by declaration name or a list, and which fields carry name / kind / module / docstring. **Write the fixture in Step 2 in EXACTLY the observed shape** and note the URL + shape in a comment at the top of `harvest.py`. If neither URL responds usefully, fall back to the per-module `declarations/*.json` layout probe: `curl -s https://leanprover-community.github.io/mathlib4_docs/searchable_data.bmp -r 0-2000`. One of these exports exists — doc-gen4 publishes machine-readable declaration data; find it, pin it, and move on (≤15 min timebox; if truly blocked, mark Task 6 deferred and proceed — v0 ships with 2 libraries + an honest "mathlib: harvest pending" card, per spec's coverage-honesty rule).

- [ ] **Step 2: Write fixture `tests/fixtures/mathlib_decls_small.json`** — 5 declarations in the observed shape: mix of `theorem` / `def` / `instance` kinds across 2 modules (e.g. `Mathlib.Analysis.SpecialFunctions.Complex.Circle` and `Mathlib.NumberTheory.Bernoulli`).

- [ ] **Step 3: Write the failing test `tests/test_mathlib.py`**

```python
import json, pathlib
from harvesters.mathlib.harvest import harvest

FIX = pathlib.Path(__file__).parent / "fixtures" / "mathlib_decls_small.json"

def test_harvest_maps_kinds_and_urls(tmp_path):
    man = harvest(source=str(FIX), out_dir=tmp_path)
    rows = [json.loads(l) for l in (tmp_path / "statements.jsonl").read_text().splitlines()]
    assert man["statement_count"] == len(rows) > 0
    kinds = {r["kind"] for r in rows}
    assert kinds <= {"theorem", "definition", "lemma", "other"}
    for r in rows:
        assert r["source_url"].startswith("https://leanprover-community.github.io/mathlib4_docs/")
        assert r["module"]
```

- [ ] **Step 4: Run to verify failure**, then **Step 5: implement `harvest.py`** following the brockian pattern: `_load()` (URL or path), a `to_statement()` mapping observed-shape → normalized (kind map: `theorem|thm→theorem`, `def|definition|structure|instance→definition`, else `other`; `source_url` = mathlib4_docs module page + `#<name>` anchor; `module` = dotted module name), `harvest()` calling `write_harvest(..., subject_derivation="Mathlib module path prefix")`. For a top-level-object shape iterate `.items()`; keep memory bounded by iterating, not materializing intermediate lists where the shape allows.

- [ ] **Step 6: Run tests** — Expected: pass. **Step 7: Commit** — `git add harvesters/mathlib/harvest.py tests/test_mathlib.py tests/fixtures/mathlib_decls_small.json && git commit -m "harvester: mathlib (doc-gen4 declaration export)"`

### Task 7: CI workflow

**Files:** Create: `.github/workflows/ci.yml`

- [ ] **Step 1: Write `ci.yml`**

```yaml
name: ci
on:
  push: {branches: [main]}
  pull_request:
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: {python-version: "3.12"}
      - run: pip install -e '.[dev]'
      - run: pytest -q
```

- [ ] **Step 2: Commit** — `git add .github/workflows/ci.yml && git commit -m "ci: pytest on push/PR"`

## Chunk 3: Concept seed (Wiedijk 100)

### Task 8: Wiedijk-100 seed builder

**Files:** Create: `tools/build_wiedijk_seed.py`, `concepts/wiedijk100.yaml`, `tests/fixtures/mathlib_100_small.yaml`, Test: `tests/test_wiedijk_seed.py`

Source of truth: mathlib4 `docs/100.yaml` (`https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/100.yaml`, confirmed reachable) — Wiedijk's numbered list with mathlib declaration names where formalized. This yields concepts (all 100) + CURATED mathlib alignments (where `decl`/`decls` present). Metamath/other-prover alignments are v1 (Wiedijk's per-prover pages need their own parser — YAGNI for v0).

- [ ] **Step 1: Grab a real excerpt for the fixture**

```bash
curl -s https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/100.yaml | head -40
```

Copy 3 entries (one with `decl`, one with `decls` list, one unformalized if present) into `tests/fixtures/mathlib_100_small.yaml` verbatim.

- [ ] **Step 2: Write the failing test `tests/test_wiedijk_seed.py`**

```python
import pathlib, yaml
from tools.build_wiedijk_seed import build_seed

FIX = pathlib.Path(__file__).parent / "fixtures" / "mathlib_100_small.yaml"

def test_build_seed_concepts_and_alignments(tmp_path):
    out = tmp_path / "wiedijk100.yaml"
    build_seed(source=str(FIX), out=str(out))
    doc = yaml.safe_load(out.read_text())
    assert doc["seed_source"] == "wiedijk100"
    concepts = doc["concepts"]
    assert len(concepts) == 3
    c = concepts[0]
    assert set(c) >= {"slug", "title", "wiedijk_number", "status", "alignments"}
    formalized = [c for c in concepts if c["alignments"]]
    for c in formalized:
        a = c["alignments"][0]
        assert a["library"] == "mathlib" and a["tier"] == "CURATED"
        assert a["evidence"]["source"] == "mathlib4 docs/100.yaml"
    unformalized = [c for c in concepts if not c["alignments"]]
    assert all(c["status"] == "open" for c in unformalized)
```

- [ ] **Step 3: Run to verify failure**, then **Step 4: write `tools/build_wiedijk_seed.py`**: parse the 100.yaml mapping (`{number: {title, decl?, decls?, authors?, links?}}`), emit:

```yaml
seed_source: wiedijk100
generated_from: mathlib4 docs/100.yaml
concepts:
  - slug: "wiedijk-001-irrationality-of-sqrt-2"   # slugified "NNN-title"
    title: "The Irrationality of the Square Root of 2"
    wiedijk_number: 1
    informal_statement: null        # curated later; never auto-filled
    msc_primary: null
    status: partially-formalized    # "open" when no alignments
    alignments:
      - library: mathlib
        native_name: "Nat.Prime.irrational_sqrt"
        tier: CURATED
        evidence: {source: "mathlib4 docs/100.yaml", field: "decl"}
```

`status`: `open` if no decls, else `partially-formalized` (v0 never claims `formalized` — that judgment is curation). Deterministic slugs; sort by number; write with `yaml.safe_dump(..., sort_keys=False, allow_unicode=True)`.

- [ ] **Step 5: Run tests** — pass. **Step 6: Generate the real seed** — `.venv/bin/python tools/build_wiedijk_seed.py --source https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/100.yaml --out concepts/wiedijk100.yaml` then `python3 -c "import yaml; d=yaml.safe_load(open('concepts/wiedijk100.yaml')); print(len(d['concepts']), 'concepts,', sum(1 for c in d['concepts'] if c['alignments']), 'with mathlib alignments')"` — Expected: 100 concepts, ~90+ aligned. Eyeball 3 entries by hand against the source.
- [ ] **Step 7: Commit** — `git add tools/build_wiedijk_seed.py concepts/wiedijk100.yaml tests/test_wiedijk_seed.py tests/fixtures/mathlib_100_small.yaml && git commit -m "seed: Wiedijk-100 concepts with CURATED mathlib alignments"`

**Note (targets board):** the Riemann `/targets` 104-problem board lives in the Lovable site's data (`dd8308ac`), not in a local file. Deferred to a v0.1 follow-up task: read via Lovable MCP `read_file` on `src/data/` (discovery), convert to `concepts/targets-board.yaml`. Do NOT block v0 on it.

## Chunk 4: Supabase (migrations + loader)

### Task 9: Migration SQL

**Files:** Create: `migrations/001_atlas_tables.sql`

- [ ] **Step 1: Write the migration** (spec §4 verbatim; RLS pattern = existing BCC/Riemann anon-read):

```sql
create table if not exists atlas_libraries (
  id text primary key,               -- slug: brockian|metamath|mathlib|...
  name text not null,
  prover text not null,
  url text not null,
  license text,
  harvester_version text,
  last_harvest_at timestamptz,
  statement_count integer not null default 0
);

create table if not exists atlas_statements (
  id bigint generated always as identity primary key,
  library_id text not null references atlas_libraries(id),
  native_name text not null,
  kind text not null,
  statement_text text,
  module text,
  source_url text not null,
  subject_codes text[] not null default '{}',
  first_seen_edition integer,
  last_seen_edition integer,
  retired boolean not null default false,
  unique (library_id, native_name)
);
create index if not exists atlas_statements_library_idx on atlas_statements(library_id);
create index if not exists atlas_statements_name_idx on atlas_statements(native_name);

create table if not exists atlas_concepts (
  id bigint generated always as identity primary key,
  slug text not null unique,
  title text not null,
  informal_statement text,
  wikidata_id text,
  wiedijk_number integer,            -- Wiedijk top-100 number, null otherwise
  msc_primary text,
  seed_source text not null,         -- wiedijk100 | targets-board | curated | llm-proposed
  status text not null default 'open',  -- open | partially-formalized | formalized
  notes text
);

create table if not exists atlas_alignments (
  id bigint generated always as identity primary key,
  concept_id bigint not null references atlas_concepts(id),
  statement_id bigint not null references atlas_statements(id),
  tier text not null check (tier in ('CURATED','ALIGNED','CANDIDATE')),
  evidence jsonb not null default '{}',
  created_by text,
  confirmed_by text,
  unique (concept_id, statement_id)
);

create table if not exists atlas_harvest_runs (
  id bigint generated always as identity primary key,
  library_id text not null references atlas_libraries(id),
  started_at timestamptz not null default now(),
  edition_tag integer,
  source_version text,
  statements_seen integer,
  added integer,
  retired integer,
  status text not null default 'running',   -- running | ok | failed
  log_url text
);

-- Policies are guarded for idempotent re-application (Lovable-MCP re-runs happen)
drop policy if exists atlas_libraries_read    on atlas_libraries;
drop policy if exists atlas_statements_read   on atlas_statements;
drop policy if exists atlas_concepts_read     on atlas_concepts;
drop policy if exists atlas_alignments_read   on atlas_alignments;
drop policy if exists atlas_harvest_runs_read on atlas_harvest_runs;

alter table atlas_libraries    enable row level security;
alter table atlas_statements   enable row level security;
alter table atlas_concepts     enable row level security;
alter table atlas_alignments   enable row level security;
alter table atlas_harvest_runs enable row level security;
create policy atlas_libraries_read    on atlas_libraries    for select to anon using (true);
create policy atlas_statements_read   on atlas_statements   for select to anon using (true);
create policy atlas_concepts_read     on atlas_concepts     for select to anon using (true);
create policy atlas_alignments_read   on atlas_alignments   for select to anon using (true);
create policy atlas_harvest_runs_read on atlas_harvest_runs for select to anon using (true);
grant select on atlas_libraries, atlas_statements, atlas_concepts, atlas_alignments, atlas_harvest_runs to anon;

insert into atlas_libraries (id, name, prover, url, license) values
  ('brockian', 'Brockian Corpus', 'Lean 4 / AXLE', 'https://torus.riemannlab.com/explore/lean-registry', 'project'),
  ('metamath', 'Metamath (set.mm)', 'Metamath', 'https://us.metamath.org', 'CC0'),
  ('mathlib',  'Mathlib', 'Lean 4', 'https://leanprover-community.github.io/mathlib4_docs/', 'Apache-2.0')
on conflict (id) do nothing;
```

- [ ] **Step 2: Apply via Lovable MCP** — `mcp__claude_ai_Lovable__query_database` against project `dd8308ac-0860-42ae-908c-41b306b58858` (Spectral/Riemann torus site). FIRST probe read-only: `select count(*) from atlas_libraries` (expect error = tables absent) and confirm which Supabase this project uses via `get_database_status`. Then apply the migration statements. Verify: `select id, statement_count from atlas_libraries order by id` → 3 rows.
- [ ] **Step 3: Commit** — `git add migrations/001_atlas_tables.sql && git commit -m "migrations: atlas_* tables, anon-read RLS, library seed rows"`

### Task 10: Loader (`atlas/load.py`) + concept sync

**Files:** Create: `atlas/load.py`, `concepts/sync_concepts.py`, Test: `tests/test_loader.py`

- [ ] **Step 1: Write the failing test `tests/test_loader.py`** — pure-function tests only (no network): batching and retire-computation logic.

```python
import pytest
from atlas.load import plan_upsert

def test_plan_upsert_computes_retired():
    existing = {"a", "b", "c"}
    harvested = [{"native_name": "a"}, {"native_name": "d"}]
    plan = plan_upsert(existing, harvested, allow_big_delta=True)
    assert plan["retire"] == {"b", "c"}
    assert plan["upsert_count"] == 2

def test_plan_upsert_empty_harvest_refuses():
    with pytest.raises(ValueError, match="refusing"):
        plan_upsert({"a"}, [])   # empty harvest = probable upstream failure; never mass-retire

def test_plan_upsert_big_delta_refuses_without_override():
    # spec §8: count deltas beyond ±20% require manual approval
    existing = {str(i) for i in range(100)}
    harvested = [{"native_name": str(i)} for i in range(70)]   # -30%
    with pytest.raises(ValueError, match="delta"):
        plan_upsert(existing, harvested)
    assert plan_upsert(existing, harvested, allow_big_delta=True)["upsert_count"] == 70

def test_plan_upsert_first_harvest_allowed():
    # empty existing set (first run) is not a delta violation
    assert plan_upsert(set(), [{"native_name": "a"}])["upsert_count"] == 1
```

- [ ] **Step 2: Verify failure**, **Step 3: write `atlas/load.py`**:
  - `plan_upsert(existing_names, rows, allow_big_delta=False)` — pure. Raises `ValueError("refusing…")` on empty harvest with non-empty existing (never mass-retire on a bad run). Raises `ValueError("…delta…")` when existing is non-empty and `abs(len(rows) - len(existing)) / len(existing) > 0.20` unless `allow_big_delta` (spec §8's ±20% gate; the override is the "manual approval" path). First harvest (empty existing) always allowed.
  - `load(out_dir, supabase_url, service_key, allow_big_delta=False)` — reads `statements.jsonl` + `manifest.json`; PostgREST calls with `apikey` AND `Authorization: Bearer` headers (both required — house pattern):
    1. Existing set: `GET /rest/v1/atlas_statements?library_id=eq.<lib>&select=native_name` with **mandatory Range-header pagination, unconditionally** — loop `Range: 0-999`, `1000-1999`, … until a short page. PostgREST's server-side `db-max-rows` cap silently truncates any single request, so a one-shot `limit=` read would corrupt the retire computation for EVERY library.
    2. Upsert in batches of 500: `POST /rest/v1/atlas_statements` with `Prefer: resolution=merge-duplicates,return=minimal` and `on_conflict=library_id,native_name`. **Explicit jsonl→row mapping:** `library`→`library_id`, all other schema fields copied by name, plus **`retired: false` on every upserted row** — a statement that was retired and reappears upstream must come back to life (merge-duplicates keeps omitted columns, so omitting `retired` would leave it dead forever).
    3. Retire: `PATCH /rest/v1/atlas_statements?library_id=eq.<lib>&native_name=in.(...)` setting `retired=true` — **the `library_id` filter is mandatory** (native_name is only unique per library; without it we'd retire same-named rows in other libraries). Batches of ≤100 names, each name percent-encoded and double-quoted inside `in.("…","…")`.
    4. Update `atlas_libraries`: `statement_count` (from manifest), `last_harvest_at`, `harvester_version`.
    5. Insert `atlas_harvest_runs` row (`status='ok'`, counts, `source_version`); on any exception during 1–4, insert with `status='failed'` and re-raise.
  - CLI: `python3 -m atlas.load --dir out/metamath [--allow-big-delta]` reading `ATLAS_SUPABASE_URL` + `ATLAS_SUPABASE_SERVICE_KEY` env (`--allow-big-delta` also honored via env `ATLAS_ALLOW_BIG_DELTA=1` so the Actions manual-approval path is an env toggle on workflow_dispatch).
  - `record_failure(library, note, supabase_url, service_key)` + CLI `python3 -m atlas.load --record-failure <lib> --note "<msg>"` — inserts an `atlas_harvest_runs` row with `status='failed'` and no counts. Used by the workflow when the HARVEST step itself dies (spec §5: a harvester failure must mark a failed run, not vanish).
- [ ] **Step 4: Tests pass**, **Step 5: write `concepts/sync_concepts.py`** — reads `concepts/*.yaml`; upserts `atlas_concepts` by slug (mapping `wiedijk_number` → the migration's `wiedijk_number` column); for each alignment resolves `statement_id` by `(library, native_name)` lookup; missing statements are reported (`ALIGNMENT PENDING: <lib>/<name> not harvested yet`) and skipped, not errored — mathlib alignments resolve only after the first mathlib harvest lands. Upserts `atlas_alignments` with `on_conflict=concept_id,statement_id`. Idempotent by construction.
- [ ] **Step 6: Commit** — `git add atlas/load.py concepts/sync_concepts.py tests/test_loader.py && git commit -m "loader: safe upsert with retire semantics + concept sync"`

## Chunk 5: Publish, schedule, frontend

### Task 11: GitHub repo + scheduled harvest + editions

**Files:** Create: `.github/workflows/harvest.yml`, `.github/workflows/edition.yml`

- [ ] **Step 1: Create the public repo and push**

```bash
cd ~/Projects/formal-atlas
gh repo create primaryhosting/formal-atlas --public --source . --push \
  --description "The Formal Atlas — harvest pipeline for a living map of machine-verified mathematics (torus.riemannlab.com/atlas)"
```

- [ ] **Step 2: Write `.github/workflows/harvest.yml`**

```yaml
name: harvest
on:
  schedule:
    - cron: "17 */6 * * *"    # brockian every 6h
    - cron: "43 5 * * *"      # mathlib daily
    - cron: "7 4 * * 1"       # metamath weekly (Mon)
  workflow_dispatch:
    inputs:
      library: {description: "brockian|metamath|mathlib|all", default: "all"}
      allow_big_delta: {description: "override the ±20% count-delta gate", default: "0"}
jobs:
  plan:
    runs-on: ubuntu-latest
    outputs:
      libraries: ${{ steps.pick.outputs.libraries }}
    steps:
      - id: pick
        run: |
          L='${{ github.event.inputs.library || 'all' }}'
          if [ "$L" = "all" ]; then
            echo 'libraries=["brockian","metamath","mathlib"]' >> "$GITHUB_OUTPUT"
          else
            echo "libraries=[\"$L\"]" >> "$GITHUB_OUTPUT"
          fi
  harvest:
    needs: plan
    runs-on: ubuntu-latest
    strategy:
      fail-fast: false
      matrix:
        library: ${{ fromJSON(needs.plan.outputs.libraries) }}
    env:
      ATLAS_SUPABASE_URL: ${{ secrets.ATLAS_SUPABASE_URL }}
      ATLAS_SUPABASE_SERVICE_KEY: ${{ secrets.ATLAS_SUPABASE_SERVICE_KEY }}
      ATLAS_ALLOW_BIG_DELTA: ${{ github.event.inputs.allow_big_delta || '0' }}
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: {python-version: "3.12"}
      - run: pip install -e .
      - name: Harvest
        run: python harvesters/${{ matrix.library }}/harvest.py --out out/${{ matrix.library }}
      - name: Load to Supabase
        run: python -m atlas.load --dir out/${{ matrix.library }}
      - name: Sync concepts
        if: matrix.library == 'mathlib'
        run: python concepts/sync_concepts.py
      - name: Record failed run
        if: failure()
        run: python -m atlas.load --record-failure ${{ matrix.library }} --note "workflow ${{ github.run_id }} failed at harvest or load"
      - uses: actions/upload-artifact@v4
        if: always()
        with: {name: "harvest-${{ matrix.library }}-${{ github.run_id }}", path: "out/${{ matrix.library }}"}
```

(Header comment in the file must note: scheduled ticks run ALL libraries — brockian's re-read is 3 MB and the others are idempotent upserts; per-library cron splitting is deferred until Actions minutes matter — YAGNI now.)

- [ ] **Step 3: Write `.github/workflows/edition.yml`** — weekly (Sun 23:00 UTC) + `workflow_dispatch`: checkout, pip install, run all three harvesters into `out/`, `tar czf edition.tar.gz out/`, compute next edition number `N` = count of existing `edition-*` releases + 1 (`gh release list`), create release `edition-N` with the tarball + a body listing per-library counts from the manifests, then run `python -m atlas.edition --tag N` (env secrets as above; the workflow needs `permissions: {contents: write}` for `gh release create`). **`atlas/edition.py` exact semantics:** (a) `PATCH atlas_statements?retired=eq.false` set `last_seen_edition=N` (unconditionally over live rows — do NOT use a `neq.N` guard: PostgREST `neq` excludes NULLs, and every row is NULL before Edition 1, so a `neq` filter would silently no-op forever), and `PATCH atlas_statements?first_seen_edition=is.null` set `first_seen_edition=N`; (b) `PATCH atlas_harvest_runs?edition_tag=is.null&status=eq.ok` set `edition_tag=N` — an edition stamps every successful run not yet shipped by a previous edition ("the edition that first shipped that data", spec §4). Header comment must acknowledge: the release tarball is a fresh harvest while the DB stamp covers the latest scheduled loads — they can differ by hours; accepted for v0.
- [ ] **Step 4: Commit + push** — `git add .github/workflows/harvest.yml .github/workflows/edition.yml atlas/edition.py && git commit -m "actions: scheduled harvests, weekly editions" && git push`

### Task 12: Secrets (HUMAN-GATED) + first live run

- [ ] **Step 1 (CHRIS): Mint the service key** — Supabase dashboard for the Riemann/torus project → Settings → API → copy the `service_role` key (the vault's `RIEMANN_SUPABASE_KEY` 401s; do not reuse it). Then:

```bash
gh secret set ATLAS_SUPABASE_URL -R primaryhosting/formal-atlas    # https://<ref>.supabase.co
gh secret set ATLAS_SUPABASE_SERVICE_KEY -R primaryhosting/formal-atlas
```

- [ ] **Step 2: Trigger and watch** — `gh workflow run harvest.yml -R primaryhosting/formal-atlas -f library=all && gh run watch -R primaryhosting/formal-atlas` — Expected: 3 green matrix jobs.
- [ ] **Step 3: Verify data** — via Lovable `query_database`: `select id, statement_count, last_harvest_at from atlas_libraries order by id` → brockian ≈11.5k, metamath ≈40k+, mathlib ≈100k+ (or honest zero + `harvest_runs.status='failed'` if an upstream shape surprised us — fix forward). `select count(*) from atlas_concepts` → 100. `select tier, count(*) from atlas_alignments group by tier` → CURATED only.
- [ ] **Step 4: Cut Edition 1** — `gh workflow run edition.yml -R primaryhosting/formal-atlas && gh run watch -R primaryhosting/formal-atlas` — Expected: release `edition-1` exists with `edition.tar.gz`; verify `select max(edition_tag) from atlas_harvest_runs` → 1, `select count(*) from atlas_statements where first_seen_edition = 1` > 0, AND `select count(*) from atlas_statements where last_seen_edition = 1` > 0 (this last one catches edition-stamp filter bugs). (Without this step the DoD's "Edition 1 exists" and the frontend's edition footer are unsatisfiable until Sunday's cron.)

### Task 13: `/atlas` frontend (Lovable `dd8308ac`) — 3 prompts + eyes-on

Frontend is built by prompting the Lovable agent (house pattern). Follow dual-theme/legibility and DepthShell register discipline; every count queries Supabase live — no hardcoded numbers.

- [ ] **Step 1: Prompt 1 — `/atlas` home + library cards.** Send via `mcp__claude_ai_Lovable__send_message` to `dd8308ac`: build route `/atlas` reading `atlas_libraries` (cards: name, prover, harvester-measured `statement_count` with `last_harvest_at` "as of" timestamp), headline strip (total statements across libraries; concepts count; alignments count **excluding CANDIDATE — enforce in the query**: `tier=in.(CURATED,ALIGNED)`), a "not yet harvested" card for AFP/Coq/HOL Light/Mizar (explicit "statement-level harvest: not yet built"), an honest-gaps line naming BOTH pending items ("4 libraries not yet harvested · targets-board concept seed pending"), footer edition tag from max `atlas_harvest_runs.edition_tag` (render "pre-edition" if null). Register in `site-registry.ts`. Link `/atlas/method`.
- [ ] **Step 2: Prompt 2 — `/atlas/method` + `/atlas/concept/:slug`.** Method page: render the canonical text (paste from brockian-mathematics `docs/atlas/METHOD.md` — verbatim, it's the contract). Concept page: title, informal statement (or "curation pending"), status chip, one verification card per alignment (library, native_name, tier chip — CURATED/ALIGNED/CANDIDATE visually distinct, CANDIDATE visibly "unconfirmed" — source link out).
- [ ] **Step 3: Prompt 3 — `/atlas/frontier`.** Concepts with `status='open'` (no verified formalization in harvested libraries) + `partially-formalized`, seeded-from labels, sorted by `wiedijk_number` (column added in migration; nulls last).
- [ ] **Step 4 (CHRIS + agent): Eyes-on.** House rule: never ship flagship UI verified only headlessly. Open preview, check both themes, verify a concept page against its Supabase rows by hand (e.g. `wiedijk-001-…`), THEN Chris clicks Publish.
- [ ] **Step 5: Record.** Update memory `formal-atlas-program.md`: v0 shipped state, edition number, any deferred items (targets-board seed, mathlib shape notes).

---

## Definition of done (v0 / Edition 1)

- `pytest -q` green in CI on `primaryhosting/formal-atlas` (public).
- Scheduled harvests green; `atlas_libraries` shows 3 live harvester-measured counts with timestamps.
- 100 Wiedijk concepts + CURATED mathlib alignments in Supabase; zero CANDIDATE rows anywhere.
- `/atlas`, `/atlas/method`, `/atlas/concept/:slug`, `/atlas/frontier` live on torus.riemannlab.com, dual-theme, every number traceable to a harvest run.
- Edition 1 release exists with attached datasets.
- Honest gaps stated on the home page (4 libraries pending; targets-board seed pending).
