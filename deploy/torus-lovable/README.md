# Torus Lovable deploy package

Generated from `brockian-mathematics` tip. **Do not hand-edit** `public/verified-registry.json`.

## Contents

| Path | Role |
|------|------|
| `src/components/verified/VerifiedClaim.tsx` | Honesty-firewall badge component |
| `src/components/verified/useVerified.ts` | Registry lookup hook |
| `public/verified-registry.json` | Sanitized registry (brockian only until Mathlib harvest) |
| `manifest.schema.json` | Lab claim → theorem binding schema |
| `LOVABLE_PROMPT.md` | Prompt to paste into Lovable |

## Regenerated from

```bash
cd ~/Projects/brockian-mathematics
python3 scripts/export_public_registry.py
# HONESTY CHECK PASSED; split-by-source [brockian] PROVED=1955 …
cp torus/public/verified-registry.json deploy/torus-lovable/public/
cp torus/VerifiedClaim.tsx torus/useVerified.ts deploy/torus-lovable/src/components/verified/
```

## Deploy steps (Lovable)

1. Open **torus.riemannlab.com** (Spectral / prime-rigor-explorer).
2. Paste `LOVABLE_PROMPT.md` (or use manager when Chrome CDP is up).
3. **Publish**.
4. Verify:
   - `Brockian.Admissibility.admissibility_count_five` → green Verified
   - `Brockian.PentagonGrandEquivalence.pentagon_grand_equivalence` → green Verified
   - `Brockian.Nonexistent.rh_is_true` → ⊘ UNVERIFIED
5. Never claim RH / Goldbach / Gate-1 closed in lab copy.

## Status (epic strike 2026-08-02)

| Item | Result |
|------|--------|
| Public registry | **2320** records · **PROVED=1955** · source brockian only |
| Honesty check | PASSED |
| Century pack | gaps 72–100 · Cos p=31/37/41 · K₂×23/31 |
| Grand Pentagon | machine-checked 4-way TFAE on tip |
| CDP | often down — paste path |
