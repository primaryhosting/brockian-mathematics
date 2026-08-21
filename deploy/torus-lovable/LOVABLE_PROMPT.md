# Lovable prompt — wire VerifiedClaim honesty firewall

**Project:** torus.riemannlab.com (Riemann Labs / Spectral / AI Mathematician)  
**Goal:** Install the verified-claim surface so public UI cannot show PROVED badges without a registry hit.  
**Honesty:** Sources never merge; CONJECTURE/CONDITIONAL never render as green verified.

## Tasks

### 1. Add components

Create these files exactly (paths may use `@/` alias if the project already has it):

- `src/components/verified/VerifiedClaim.tsx`
- `src/components/verified/useVerified.ts`

Copy content from the repo package:

- `deploy/torus-lovable/src/components/verified/VerifiedClaim.tsx`
- `deploy/torus-lovable/src/components/verified/useVerified.ts`

If you cannot read the host filesystem, the operator will paste the two TypeScript files in the next message. Keep them side-by-side so `import { useVerified } from "./useVerified"` resolves.

### 2. Static registry asset

Place `public/verified-registry.json` at the site root public path so it is served as:

`/verified-registry.json`

Source file: `deploy/torus-lovable/public/verified-registry.json` (sanitized).
Do not minify away the `summary` or `theorems` arrays. Do not invent extra PROVED rows.

### 3. Demo mount (required for verification)

On a low-traffic admin or “Verification” panel (or bottom of About), render:

```tsx
import { VerifiedClaim } from "@/components/verified/VerifiedClaim";

export function VerificationHonestyDemo() {
  return (
    <div className="space-y-3 p-4">
      <h2 className="text-lg font-semibold">Verification honesty demo</h2>
      <VerifiedClaim
        claim="Exactly 3 admissible start residues mod 5 for a nonzero gap (q−ν law)"
        theorem="Brockian.Admissibility.admissibility_count_five"
      />
      <VerifiedClaim
        claim="For prime p: p=5 ⇔ φ−1 ∈ spec(C_p) ⇔ [ℚ(2cos 2π/p):ℚ]=2 ⇔ 2cos(2π/p)=φ−1"
        theorem="Brockian.PentagonGrandEquivalence.pentagon_grand_equivalence"
      />
      <VerifiedClaim
        claim="The Riemann Hypothesis is true"
        theorem="Brockian.Nonexistent.rh_is_true"
      />
      <p className="text-sm opacity-70">
        First two badges must resolve from /verified-registry.json (green Verified).
        RH badge must show ⊘ UNVERIFIED. Never call open problems “verified.”
      </p>
    </div>
  );
}
```

Wire this component into an existing route (About, Observatory, or Settings). Do **not** put it only in dead code.

### Epic optional: Why Five panel

If the site has an Observatory / Labs route, also mount claims from
`torus/labs/why-five-grand.manifest.json` (each `theorem` field → `VerifiedClaim`).
Do **not** invent extra PROVED rows.

### Required: Riemann Gate 1 panel

Mount every claim from:

`public/labs/riemann-gate1-operator.manifest.json`

Render each `theorem` through `VerifiedClaim`. The five `PROVED` claims must be
green. `Brockian.RiemannScaffold.RH_of_BrockianSystem` is `CONDITIONAL` and must
remain amber/open. Its implication does not construct a BrockianSystem and does
not prove RH.

### 4. Copy / counter hygiene (P0 honesty)

If the site still shows hard-coded “53 theorems / 41 proved / dual Lean+Rocq verified / premier / on-chain verified / Proving the unprovable”, replace or soft-gate:

- Prefer live counts from `verified-registry.json` → `summary` / by_register if present.
- Remove “on-chain verified” and “proving the unprovable”.
- Dual Lean+Rocq: only if both backends resolve; otherwise say “Lean 4 + Mathlib; Rocq optional”.
- Open problems (RH, global Goldbach, oscillator ESA, compact resolvent, and the RH spectral correspondence) must never use a green Verified badge.
- The bounded-continuous-potential Gate-1 theorem may render green only under its exact registered statement.

### 5. Acceptance checks

- [ ] `/verified-registry.json` returns 200 JSON with theorems array.
- [ ] Demo PROVED theorem shows green Verified.
- [ ] Concrete bounded-potential Gate-1 theorem shows green Verified.
- [ ] `RH_of_BrockianSystem` shows amber Conditional/open, never green.
- [ ] Fake theorem shows red ⊘ UNVERIFIED (not a spinner forever).
- [ ] No new claim of RH/Goldbach solved.
- [ ] Publish to production CDN.

### 6. Non-goals

- Do not rebuild the Lean registry in the browser.
- Do not merge Mathlib/Physlib index counts until those sources appear in the JSON `source` facet.
- Do not call AXLE from the frontend.

---

## 4. The Brockian System lab (2026-08-21)

Add a **"The Brockian System"** page (route `/labs/brockian-system`, and a card in
the Observatory/Labs index). Render every claim in
`public/labs/brockian-system.manifest.json` through `<VerifiedClaim claim=… theorem=…/>`,
in manifest order — it reads as a narrative from the mod-5 structure of the number
line, through the depth-holonomy no-go (now complete in both directions), the D5
character layer, Vaughan's identity (Bombieri–Vinogradov Layer 4), to the honest
conditional frontier.

Honesty is enforced by the component, not by you:
- The 9 `PROVED` claims render green Verified badges.
- The 3 `CONDITIONAL` claims (Twin⇐Dickson, Brocard⇐ABC, Euclid–Euler equivalence)
  MUST render as the distinct **open / not-a-proof** state — never green. The manifest
  labels them "CONDITIONAL:" in the claim text; keep that prefix visible.
Do NOT invent extra PROVED rows. Do NOT upgrade any conditional to verified.

## 5. Viewpoint — "The Black Swan"

Add a **Viewpoints** section (or a single page at `/viewpoint/the-black-swan`) that
renders `public/viewpoints/the-black-swan.md`.

This is EDITORIAL, not a lab. It must be visually and semantically distinct from the
verified labs:
- Show the front-matter `honesty` disclaimer prominently at the top ("This is a
  viewpoint … not a verified claim … nothing here should render a green badge").
- Do NOT attach VerifiedClaim badges to anything in this essay. It is argument, not
  proof. No green Verified styling anywhere on the page.
- Render the markdown (front-matter `title`/`subtitle`/`date` as the header; body as
  prose). Twelve numbered ideas plus the bounded/unbounded framing.

The point of the firewall is that a reader can always tell three states apart:
**verified** (green, theorem-backed), **conditional/conjecture** (open, explicitly not
a proof), and **viewpoint** (editorial, no badge at all). This viewpoint is the third.
