# Torus Lovable deploy package (Grok handoff — step 1)

Generated from `brockian-mathematics` tip. **Do not hand-edit** `public/verified-registry.json`.

## Contents

| Path | Role |
|------|------|
| `src/components/verified/VerifiedClaim.tsx` | Honesty-firewall badge component |
| `src/components/verified/useVerified.ts` | Registry lookup hook |
| `public/verified-registry.json` | Sanitized registry (brockian only until Mathlib/Physlib harvest) |
| `manifest.schema.json` | Lab claim → theorem binding schema |
| `LOVABLE_PROMPT.md` | Prompt to paste into Lovable (spectral / torus site) |

## Regenerated from

```bash
cd ~/Projects/brockian-mathematics
python3 scripts/export_public_registry.py
# HONESTY CHECK PASSED; split-by-source [brockian] PROVED=1832 …
cp torus/public/verified-registry.json deploy/torus-lovable/public/
cp torus/VerifiedClaim.tsx torus/useVerified.ts deploy/torus-lovable/src/components/verified/
```

## Deploy steps (Lovable)

1. Open the **torus.riemannlab.com** Lovable project (Spectral / prime-rigor-explorer; id historically `dd8308ac-…`).
2. Paste `LOVABLE_PROMPT.md` into the agent (or use manager when Chrome CDP is up).
3. After files land: **Publish**.
4. Verify preview:
   - One badge with `Brockian.Admissibility.admissibility_count_five` → green **Verified**.
   - One badge with `Brockian.Nonexistent.rh_is_true` → red **⊘ UNVERIFIED** (name must not exist in registry).
5. Do **not** change any lab copy to claim RH/Goldbach/Gate-1 closed.

## Status (2026-08-02 — Grok 1+2+3 pass)

| Item | Result |
|------|--------|
| Public registry | **2195** records; **PROVED=1832** source **`brockian` only** |
| Honesty check | **PASSED** (allowlist strip; split-by-source) |
| Demo theorem | `admissibility_count_five` present as PROVED |
| Negative demo | `Brockian.Nonexistent.rh_is_true` **absent** (UNVERIFIED path) |
| Lovable Manager | `:18793` health OK |
| Chrome CDP | **DOWN** (`:18800` / `:9222`) — `lovable_projects` returns 500; **paste** `LOVABLE_PROMPT.md` + upload `public/verified-registry.json` |
| Mathlib/Physlib index | Pending off-Mini harvest → then re-export shows multi-source split |

## Acceptance demo (after publish)

| Badge claim | Theorem id | Expected UI |
|-------------|------------|-------------|
| Exactly 3 admissible start residues mod 5… | `Brockian.Admissibility.admissibility_count_five` | Green verified (brockian/AXLE) |
| The Riemann Hypothesis is true | `Brockian.Nonexistent.rh_is_true` | Red ⊘ UNVERIFIED |
