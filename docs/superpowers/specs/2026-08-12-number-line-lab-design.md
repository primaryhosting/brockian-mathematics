# /labs/number-line — "The Number Line" flagship (design)

Date: 2026-08-12 · Site: torus.riemannlab.com (Lovable dd8308ac) · Status: approved by Chris

## Purpose

The canonical public telling of the Brockian program's founding move: the history of the
straight number line (epic scroll-story), why it is incomplete as an *arithmetic* instrument,
and the hands-on construction of the Curved Number Line B(n) = n·ω^{n−1}. The page is also a
demonstration of the honesty machinery: every mathematical claim wears its observatory chip,
including the one that is OPEN.

Audience: general public first; every claim registry-honest. Chris's design brief: "this is
the time we can show out with design and historical detail and then why ours exists and how
to construct it — next level interesting and design."

## Decisions (Chris, 2026-08-12)

- History: **epic scroll-story** (~6 eras, distinct visual treatments)
- Construction: **interactive curl animation** (scrubber morphs straight line → five rays → pentagon)
- Chips: **full treatment** — every claim badged, OPEN shown honestly
- Single continuous scroll (not chaptered); 2D canvas (no three.js)

## Structure — seven acts

1. **Hook** — full-viewport breathing straight line. "The first mathematical object you ever
   met. Five thousand years to build. It may not be finished."
2. **Epic history** — six eras, each: year marker, one artifact visual, ≤3 sentences, one
   "what was still missing" line. (1) Ishango tally ~20,000 BC; (2) Babylon/Egypt base-60;
   (3) Greece — magnitudes, √2 scandal, no zero; (4) Brahmagupta 628 — zero + negatives;
   (5) Descartes 1637 — the axis; (6) Dedekind/Cantor 1872 — the continuum complete.
   Act ends: complete but straight — primes on it look like static.
3. **Why ours exists** — straight line with primes as noise; "what if the line itself
   remembered arithmetic?"
4. **The construction (centerpiece)** — CurlCanvas with a CURL scrubber:
   t=0 straight; scrub → each n keeps radius n, turns 72° per step → B(n)=n·ω^{n−1} with live
   equation readout; five rays colorized by residue mod 5; primes toggle (ray 0 goes dark —
   four active rays); connect first five points → pentagon, side vs golden diagonal.
   Chips: BM-MAP-001, BM-PRIME-001, GEOM-C5.
5. **Why five** — pentagon λ₂ = φ−1 = 2cos(2π/5); golden ratio unique to five.
   Chips: SPEC-GOLDEN-FIVE, AUT-D5. Cross-link to the why-five lab.
6. **What the curved line sees** — twin transitions, only three roads (1→3, 2→4, 4→1),
   animated (chip BM-TRANS-001); helix return question shown as **OPEN** (BM-RET-001).
7. **Honesty footer** — "every green chip is a machine-checked Lean theorem"; links to
   Observatory, registry, fleet catalogue.

## Chips — verbatim registry contract

Claim cards carry: observatory claim ID, title verbatim from observatory/claims.json,
status (proved→PROVED chip / open→OPEN chip), linked Lean declaration names verbatim.

| Claim | Status | Lean decls (verbatim) | Honesty note shown |
|---|---|---|---|
| BM-MAP-001 | PROVED | Brockian.Core.fifth_root_of_unity, Brockian.Core.cos_2pi_5 | chip covers the cyclotomic/φ identities underwriting the map |
| BM-PRIME-001 | PROVED | Brockian.Core.each_ray_has_infinitely_many_primes | Dirichlet imported via Mathlib |
| GEOM-C5 | PROVED | Brockian.Geometry.pentagon_two_distances, .pentagon_golden_diagonal, .golden_ratio_in_C5_spectrum, .d5_card | — |
| SPEC-GOLDEN-FIVE | PROVED | Brockian.Spectral.golden_unique_to_five, Brockian.Connectivity.pentagon_lambda2_phi, .lambda2_eq | — |
| AUT-D5 | PROVED | Brockian.Automorphism.dihedral_action_faithful | faithful action; full Aut(C₅)≅D₅ iso NOT claimed |
| BM-TRANS-001 | PROVED | Brockian.TransitionKernel.forbidden_transition, .kernel_row_sum, .brockian_table_card | grammar of jumps; twin-prime infinitude NOT claimed |
| BM-RET-001 | **OPEN** | (none) | formalization still a queued target — shown as open |

Rules: PROVED chips only for names present verbatim in /verified-registry.json (live check
via useRegistryPresence); statuses come from claims.json, never hand-painted; the three
honesty notes above are mandatory copy.

## Design language

History eras: warm parchment/artifact treatments inside the site's design system. At the
moment of the curl (Act IV) the page shifts to the site's dark cosmic aesthetic — the visual
turn IS the mathematical turn. Wide editorial typography, generous spacing; era artwork as
inline SVG/CSS (no heavy image payloads).

## Tech

- Route `/labs/number-line`, registered in the site lab registry; NumberLinePage + CurlCanvas
  (2D canvas, requestAnimationFrame, scrubber-driven param t∈[0,1]; angle(n) = t·(n−1)·72°,
  radius n on a log-compressed scale for display) + eras data file.
- Golden tests pin: the seven claim IDs + statuses, the three honesty notes, and the map
  formula string "B(n) = n·ω^{n−1}" verbatim.
- Publish gate: browser eyes-on render (desktop + mobile widths), zero console errors,
  chips live-verified against prod registry, then deploy.

## Build plan (Lovable, staged)

1. Stage 1 — route + seven-act skeleton, full history copy + era design, chips as data-driven
   claim cards (statuses hardcoded from claims.json + live registry presence check), honesty
   footer. Golden tests.
2. Stage 2 — CurlCanvas centerpiece (scrub morph, residue colors, primes toggle, pentagon
   overlay), twin-roads animation, polish pass, mobile.
3. Gate + publish.
