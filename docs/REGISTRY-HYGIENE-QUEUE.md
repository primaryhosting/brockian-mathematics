# Registry Hygiene Queue

This queue tracks attestation-file hygiene only. It is deliberately not a proof
verification report and does not authorize automatic removal of any file.

## Scope

- Read-only inputs: `Brockian.lean` and `registry/attestations/*.json`.
- Generated outputs such as `registry/theorems.json` are not modified here.
- Lean proof files, provenance, and root imports are out of scope for this queue.
- Cleanup commands below are for a human/integrator after reviewing the diffs.

## Helper

Run:

```bash
python3 scripts/list_attestation_smells.py
```

Validate the helper with:

```bash
python3 -m py_compile scripts/list_attestation_smells.py
```

The helper is stdlib-only and read-only. It reports:

- duplicate attestation JSON files that claim the same Lean namespace module;
- short-name duplicates where a root-import-stem attestation already exists;
- attestations ignored by the root-import-filtered registry;
- root imports without a same-stem attestation;
- attestation JSON files whose `module_verified` field is not `true`.

## Current Smells

As of 2026-08-02, the focused helper reports two duplicate module families.

### `Brockian.Weyl.FourierMultiplier`

- Canonical candidate: `registry/attestations/WeylFourierMultiplier.json`
- Noncanonical duplicate: `registry/attestations/FourierMultiplier.json`
- Reason: `Brockian.lean` imports `Brockian.WeylFourierMultiplier`, so the canonical
  root-import-stem attestation is `WeylFourierMultiplier.json`.
- Extra issue: the short-name duplicate has `module_verified = false`, while the
  canonical attestation has `module_verified = true`.

Review:

```bash
diff -u registry/attestations/WeylFourierMultiplier.json registry/attestations/FourierMultiplier.json
```

Cleanup, only after review:

```bash
rm -- registry/attestations/FourierMultiplier.json
```

### `Brockian.Goldbach.LocalWheel`

- Canonical candidate: `registry/attestations/GoldbachLocalWheel.json`
- Noncanonical duplicate: `registry/attestations/LocalWheel.json`
- Reason: `Brockian.lean` imports `Brockian.GoldbachLocalWheel`, so the canonical
  root-import-stem attestation is `GoldbachLocalWheel.json`.
- Both files currently report `module_verified = true`.

Review:

```bash
diff -u registry/attestations/GoldbachLocalWheel.json registry/attestations/LocalWheel.json
```

Cleanup, only after review:

```bash
rm -- registry/attestations/LocalWheel.json
```

## Root-Import / Attestation Mismatches

Current non-root attestations:

- `registry/attestations/AdmissibilityCriterionScaffold.json`
- `registry/attestations/EquidistributionDeviationBound.json`
- `registry/attestations/EquidistributionFiniteScaffold.json`
- `registry/attestations/FourierMultiplier.json`
- `registry/attestations/LocalWheel.json`
- `registry/attestations/RiemannXiFunctionalEquation.json`
- `registry/attestations/WeylKatoRangeDensity.json`

The duplicate cleanup candidates are only:

- `registry/attestations/FourierMultiplier.json`
- `registry/attestations/LocalWheel.json`

The other non-root attestations are verified attestation files without a matching
root import. They should not be removed by this hygiene queue. The safe follow-up
is an integration decision: either root-import the corresponding Lean module in
a separate proof-integration change, or document that the attestation is parked
outside the root-import-filtered registry.

Review commands for the non-duplicate mismatches:

```bash
python3 -m json.tool registry/attestations/AdmissibilityCriterionScaffold.json
python3 -m json.tool registry/attestations/EquidistributionDeviationBound.json
python3 -m json.tool registry/attestations/EquidistributionFiniteScaffold.json
python3 -m json.tool registry/attestations/RiemannXiFunctionalEquation.json
python3 -m json.tool registry/attestations/WeylKatoRangeDensity.json
rg '^import Brockian\\.(AdmissibilityCriterionScaffold|EquidistributionDeviationBound|EquidistributionFiniteScaffold|RiemannXiFunctionalEquation|WeylKatoRangeDensity)$' Brockian.lean
```

Current root imports without same-stem attestations, reported by the helper:

- `Sanity`

This appears normal: `Brockian.Sanity` is a root support import rather than a
registered theorem module.

## Integration Discipline

When cleanup is approved, use explicit paths only:

```bash
git status --short -- registry/attestations/FourierMultiplier.json registry/attestations/LocalWheel.json
diff -u registry/attestations/WeylFourierMultiplier.json registry/attestations/FourierMultiplier.json
diff -u registry/attestations/GoldbachLocalWheel.json registry/attestations/LocalWheel.json
rm -- registry/attestations/FourierMultiplier.json registry/attestations/LocalWheel.json
python3 scripts/list_attestation_smells.py
python3 scripts/audit_registry_consistency.py --strict --limit 20
git add -u registry/attestations/FourierMultiplier.json registry/attestations/LocalWheel.json
git commit -m "chore(registry): remove noncanonical duplicate attestations"
```

Do not use `git add -A` for this cleanup.
