# Torus Lovable deploy package

Generated from `brockian-mathematics` tip. **Do not hand-edit** `public/verified-registry.json`.

## Contents

| Path | Role |
|------|------|
| `src/components/verified/VerifiedClaim.tsx` | Honesty-firewall badge component |
| `src/components/verified/useVerified.ts` | Registry lookup hook |
| `public/verified-registry.json` | Sanitized registry (brockian only until Mathlib harvest) |
| `public/labs/riemann-gate1-operator.manifest.json` | Verified Gate-1 claims plus the conditional RH boundary |
| `manifest.schema.json` | Lab claim → theorem binding schema |
| `LOVABLE_PROMPT.md` | Prompt to paste into Lovable |

## Regenerated from

```bash
cd ~/Projects/brockian-mathematics
python3 scripts/export_public_registry.py
# HONESTY CHECK PASSED; split-by-source [brockian] PROVED=10568
cp torus/public/verified-registry.json deploy/torus-lovable/public/
cp torus/VerifiedClaim.tsx torus/useVerified.ts deploy/torus-lovable/src/components/verified/
cp torus/labs/riemann-gate1-operator.manifest.json deploy/torus-lovable/public/labs/
```

## Deploy steps (Lovable)

1. Open **torus.riemannlab.com** (Spectral / prime-rigor-explorer).
2. Paste `LOVABLE_PROMPT.md` (or use manager when Chrome CDP is up).
3. **Publish**.
4. Verify:
   - `Brockian.Admissibility.admissibility_count_five` → green Verified
   - `Brockian.PentagonGrandEquivalence.pentagon_grand_equivalence` → green Verified
   - `Brockian.Weyl.KatoConcreteApplication.schrodinger_essentiallySelfAdjoint_via_kato_rellich` → green Verified
   - `Brockian.RiemannScaffold.RH_of_BrockianSystem` → amber Conditional / open
   - `Brockian.Nonexistent.rh_is_true` → ⊘ UNVERIFIED
5. Never claim RH, global Goldbach, oscillator ESA, or compact resolvent. Gate 1 is closed only for the stated concrete bounded continuous potentials.

## Status (operator refresh 2026-08-03)

| Item | Result |
|------|--------|
| Public registry | **11216** records · **PROVED=10568** · **DEFINITION=581** · **CONDITIONAL=20** · **DISCHARGED=7** · **CONJECTURE=40** |
| Honesty check | PASSED |
| Gate 1 | Concrete bounded-continuous-potential ESA verified; bounded Kato-Rellich verified |
| RH boundary | Spectral correspondence remains CONDITIONAL; prime-Gaussian potential is proved non-confining |
| CDP | often down — paste path |
