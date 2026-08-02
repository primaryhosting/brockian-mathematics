# Dependency Firewall

`scripts/audit_dependency_firewall.py` is a read-only overclaim audit for the
registry. It implements next-39 item #35: a conservative check that PROVED
registry entries are not being cited as independent when their metadata points
back to open CONDITIONAL or CONJECTURE nodes.

## What It Checks

The script reads:

- `registry/theorems.json`
- `provenance/verdicts.yaml`, when present

It reports warning-only findings for:

- direct references from a PROVED entry's registry/provenance text to an open
  declaration name;
- references from a PROVED entry's registry/provenance text to a module that
  contains open declarations;
- modules that contain both PROVED entries and open entries.

The audit is intentionally conservative. A finding means "inspect this before
citing it as independent." It does not rewrite the registry and does not modify
Lean files.

## Limitations

The registry does not currently encode Lean's full transitive dependency graph,
so this script is not a proof that no theorem depends on an open hypothesis.
It is a provenance firewall: it catches suspicious citations and mixed-module
risks using only the generated registry plus hand-authored provenance notes.

In particular:

- a LOW mixed-module finding may be harmless if the PROVED theorem does not use
  the open theorem;
- a clean run does not replace AXLE, `#print axioms`, no-theater lint, or Lean
  import/dependency audits;
- if `provenance/verdicts.yaml` grows beyond the current run/override shape, the
  fallback parser may ignore unsupported YAML fields. Registry-embedded
  provenance still participates in the audit.

## Local Usage

Run the audit from the repo root:

```bash
python3 scripts/audit_dependency_firewall.py
```

Show more or fewer detailed findings:

```bash
python3 scripts/audit_dependency_firewall.py --max-findings 200
```

For a stricter CI mode that fails only on direct open-declaration citations:

```bash
python3 scripts/audit_dependency_firewall.py --fail-on-high
```

The default exit code is zero because the audit is advisory. This makes it safe
to add to dashboards and pre-release reports without blocking unrelated proof
work on conservative LOW findings.

## Suggested CI Placement

Use this after registry generation and before publishing theorem counts:

```bash
python3 scripts/gen_registry.py
python3 scripts/audit_registry_opens.py
python3 scripts/audit_dependency_firewall.py --fail-on-high
```

The intended invariant is:

> No PROVED theorem should be advertised as independent while its provenance
> cites an open CONDITIONAL or CONJECTURE as an input.

When the audit reports a HIGH finding, either downgrade the theorem/register,
rewrite the provenance to identify the open input as a hypothesis, or split the
module so the open node and closed theorem are represented separately.
