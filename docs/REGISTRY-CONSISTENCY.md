# Registry Consistency Audit

`scripts/audit_registry_consistency.py` is a read-only firewall for the derived theorem registry.
It does not regenerate `registry/theorems.json`, edit provenance, or touch Lean files.

## Purpose

The audit checks the failure modes that have repeatedly mattered in the Brockian pipeline:

- every `CONDITIONAL` entry has an explicit `conditional_rung` in `{classical, literature, open}`;
- every `CONJECTURE` entry is a nullary `Prop` container, not a theorem disguised as an open claim;
- open entries carry ledger/provenance notes;
- duplicate declaration names are visible;
- stale open containers are flagged if a matching `PROVED` declaration appears in the same module;
- noncanonical attestation files are visible when they are not imported by `Brockian.lean`;
- attestation truth-gate (2026-08-17): an attestation whose `module_verified` is not true, any
  declaration recording `sorryAx` in its axioms, `axioms_ok: false`, or an `axle_verdict` of
  `"failed"` is an `ERROR` — a sorry-backed or AXLE-failed module can no longer pass `--strict`;
- register invariants (2026-08-17): the invariant is re-derived on `registry/theorems.json` entries
  themselves — a `PROVED` entry with axioms outside `ALLOWED_AXIOMS`, a truthy
  `sorry`/`native_decide`/`exact_search` flag, an axle verdict other than `"verified"`, or a non-null
  `conditional_rung` is `ERROR` proved-invariant (missing/wrong-typed fields are `ERROR`
  proved-malformed); `CONDITIONAL`/`DISCHARGED` entries recording `sorryAx` or `flags.sorry` are
  `ERROR` open-register-sorry. `ALLOWED_AXIOMS` is kept textually in sync with
  `scripts/gen_registry.py`;
- `PROVED` provenance notes containing open-strength language are surfaced for review.

The script is intentionally conservative. It reports smells; it does not decide mathematical truth.
The default exit status is `0` so it is safe for exploratory local runs. Use `--strict` when CI should
fail on `ERROR` findings.

Note: as of 2026-08-17 the live repo has 37 strict `ERROR`s, all pre-existing attestation smells
confined to the unproven ConstellationSpectralFinal attestation; `--strict` is expected to exit 1
until that attestation is resolved. Do not weaken the gate to make CI green — that silently re-opens
the hole where a sorry-backed module passes.

## Usage

```bash
python3 scripts/audit_registry_consistency.py
python3 scripts/audit_registry_consistency.py --limit 0
python3 scripts/audit_registry_consistency.py --strict
```

Validation:

```bash
python3 -m py_compile scripts/audit_registry_consistency.py
python3 scripts/audit_registry_consistency.py
python3 -m pytest tests/test_audit_registry_consistency.py  # 17 tests: attestation truth-gate + register invariants + --strict exit contract
```

## Inputs

- `registry/theorems.json`
- `provenance/verdicts.yaml`
- `Brockian.lean`
- `registry/attestations/*.json`
- source files referenced by `CONJECTURE` entries, only for the nullary-`Prop` shape check

The implementation is stdlib-only. If PyYAML is installed, the audit also cross-checks YAML run and
override provenance against the registry; otherwise it falls back to registry-embedded provenance fields.

## Interpreting Findings

`ERROR` means the registry shape is internally inconsistent or its truth posture is violated: for
example a conditional without a valid rung, a conjecture that is not a nullary `Prop` container, a
duplicate full declaration name, a stale embedded summary, a sorry-backed, unverified, or AXLE-failed
attestation, or a registry entry violating its register invariant.

`WARN` means there is likely coordination work to do: for example an attestation file exists for a
module that is not root-imported (existence-without-root-import stays `WARN`; attestation *truth*
failures are `ERROR`), or an open entry has missing YAML provenance.

`INFO` means human review is useful but the pattern is often intentional. In particular, many `PROVED`
entries inherit run-level notes that explicitly say what the module does not prove. Those notes are good
scientific hygiene, but the audit still lists them so open-strength language inside proved rows remains
visible.

## Current Scope

This audit is for registry consistency, not proof verification. It complements, but does not replace:

- AXLE checks;
- `#print axioms` probes in attestations;
- `scripts/no_theater_lint.py`;
- the root-import filter in `scripts/gen_registry.py`;
- explicit-path integration discipline for concurrent agents.
