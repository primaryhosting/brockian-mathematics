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
- `PROVED` provenance notes containing open-strength language are surfaced for review.

The script is intentionally conservative. It reports smells; it does not decide mathematical truth.
The default exit status is `0` so it is safe for exploratory local runs. Use `--strict` when CI should
fail on `ERROR` findings.

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

`ERROR` means the registry shape is internally inconsistent: for example a conditional without a valid
rung, a conjecture that is not a nullary `Prop` container, a duplicate full declaration name, or a stale
embedded summary.

`WARN` means there is likely coordination work to do: for example an attestation file exists for a module
that is not root-imported, or an open entry has missing YAML provenance.

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
