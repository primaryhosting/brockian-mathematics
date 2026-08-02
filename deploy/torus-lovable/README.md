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
# HONESTY CHECK PASSED; split-by-source [brockian] PROVED=1487 …
cp torus/public/verified-registry.json deploy/torus-lovable/public/
cp torus/VerifiedClaim.tsx torus/useVerified.ts deploy/torus-lovable/src/components/verified/
```

## Deploy steps (Lovable)

1. Open the **torus.riemannlab.com** Lovable project (Spectral / prime-rigor-explorer; id historically `dd8308ac-…`).
2. Paste `LOVABLE_PROMPT.md` into the agent (or use manager when Chrome CDP is up).
3. After files land: **Publish**.
4. Verify preview:
   - One badge with `Brockian.Admissibility.admissibility_count_five` → green **Verified**.
   - One badge with `Brockian.Nonexistent.rh_is_true` → red **⊘ UNVERIFIED**.
5. Do **not** change any lab copy to claim RH/Goldbach/Gate-1 closed.

## Status (2026-08-02)

- Public registry: **1824** records, source **`brockian` only** (Mathlib/Physlib index pending off-Mini harvest).
- Lovable Manager API: health OK; project list via CDP **blocked** this session (Chrome :18800 not reachable) — use paste prompt or restore OpenClaw browser profile.
