# Super Labs Program — 50 Labs, Progressive Quality Ratchet

**Directive (Chris, 2026-08-09):** 50 new labs, each progressively better, the first as good as the best we currently have (the Zeta Observatory pattern).

## The quality bar

**Base bar — EVERY lab, starting with Lab 1** (this IS the Observatory pattern):
- `DepthShell` three depths: Surface (one polished cinematic scene w/ stills fallback + `?forceStills=1`), Explore (live kernel-worker compute), Rigor (claims with register badges).
- New kernel tasks get golden Vitest tests; all compute off the main thread; ProvenanceStrip on every output.
- Claims in a per-lab `claims.ts`; PROVED only with a theoremName verified VERBATIM in `/public/verified-registry.json` (omit/downgrade, never invent); integrity test covers it; RH/open questions marked OPEN.
- Registered in `src/config/site-registry.ts`; 0 console errors; first-class empty/error states; honest copy.
- Scope note: the Observatory's Surface is a 4-chapter journey; lab Surfaces are ONE chapter-quality scene. Everything else matches.

**The ratchet — each block of 5 labs adds one capability, kept by all later labs:**
- R1 (labs 1–5): base bar.
- R2 (6–10): + shareable state — all Explore params serialize to the URL (permalink any configuration).
- R3 (11–15): + guided tour — a "walk me through it" stepper on the Explore layer.
- R4 (16–20): + data export — computed series downloadable as CSV/JSON with an embedded provenance header.
- R5 (21–25): + comparative overlays — every plot can overlay a second configuration for A/B.
- R6 (26–30): + sonification where meaningful (Web Audio, muted by default) or an equivalent second modality.
- R7 (31–35): + challenge mode — one verifiable "find/predict X" interaction per lab.
- R8 (36–40): + a11y pass — keyboard-complete, aria labels on all viz, contrast-checked.
- R9 (41–45): + perf instrumentation — visible frame/compute budget readout; degrades gracefully.
- R10 (46–50): + cross-lab links — related-lab rail resolved from the site registry; Lab 50 is the capstone Atlas aggregating all of it.

## The 50

**A — Primes & Distribution:** 1. π(x) vs Li(x) Race · 2. Prime Gaps Explorer · 3. Andrica Lab · 4. Twin Primes & Constellations · 5. Goldbach Comb
**B — Zeta Analytics:** 6. Critical Line Walker · 7. Zeta Landscape Explorer (pan/zoom gridAbs) · 8. Explicit Formula Orchestra · 9. Montgomery Pair Correlation · 10. Riemann–Siegel Anatomy
**C — Brockian Program:** 11. Five-Point Alphabet Deep Lab · 12. Metallic Means Spectra · 13. Pentagon Isotypic Lab · 14. Euler Pentagonal Lab · 15. Weyl Scaffold Lab
**D — Randomness & Structure:** 16. Gilbreath Triangle · 17. Benford & First Digits · 18. Random Matrix Ensembles (GOE/GUE/GSE) · 19. Continued Fractions & Metallic Numbers · 20. Kadison–Singer / Sensitivity
**E — Classical Named Theorems (`ms-*` PROVED set):** 21. Mason–Stothers · 22. Zeckendorf · 23. Erdős–Szekeres · 24. Cauchy–Davenport · 25. Machin π
**F — The Aristotle Harvest I (corpus-first, per Chris's directive):** 26. The Singular Series Atlas (6,322 PROVED Gaps<N> constants — the crown of the harvest) · 27. Character Table of the Pentagon (D5 cluster ~147 PROVED) · 28. Penrose Tiling Lab (41 PROVED) · 29. The Twin Prime Constant (26 PROVED) · 30. Perfect Numbers & Mersenne (15 PROVED, Euclid–Euler)
**G — The Aristotle Harvest II:** 31. Galois: Why Five (17 PROVED, quintic) · 32. Recreational Primes (Palindromic 17 + RuthAaron 15 + Polignac 19 PROVED) · 33. Franklin's Involution Deep Lab (FranklinFixedPoint 34 + MapConstruction 16) · 34. The Schrödinger Minimal Lab (Weyl.SchrodingerMinimal 17 + Confining 20+18) · 35. Golden Uniqueness & the Connectivity Bridge (20 + 22 PROVED)
**H — Number Theory Classics:** 36. Gauss–Wilson · 37. Quadratic Reciprocity · 38. Chinese Remainder + Admissibility · 39. Farey & Ford Circles · 40. Collatz Observatory (OPEN, honest)
**I — Probability & Information:** 41. Central Limit / Galton · 42. Shannon Entropy Lab · 43. Random Walks & Pólya Recurrence · 44. Percolation Threshold · 45. Coupon Collector
**J — Geometry, Physics & Capstone:** 46. Pentagon Tilings & Golden Spirals · 47. Sphere Packing Story · 48. Quantum Harmonic Oscillator Ladder · 49. Weyl Equidistribution · 50. **The Grand Atlas** — capstone: cross-lab map + registry coverage dashboard.

Registry-citation rule everywhere: resolve exact names from `/public/verified-registry.json` at build time; absent ⇒ omit or downgrade. Known: the sanitized public registry differs from the local `registry/theorems.json` (e.g. `ConstellationSpectrum` is local-only; `Brockian.Sieve.H3_*` are public) — the PUBLIC file is the only authority for the site.

**Execution:** one Lovable build message per lab (Lab 1 gets an extra verification pass), sequential; verify (kernel tests + typecheck + 0 console errors) each before the next; publish gates remain eyes-on-only. Prereq: Observatory Rigor layer (ClaimRef/ProofChip primitives) — in flight.

**Status (2026-08-09):** Rigor primitives ✅ (generalized, CLASSICAL register + ClaimSetContext) · Observatory 3-depth COMPLETE (unpublished, eyes-on pending) · Fleet pipeline wired, awaiting RIEMANN_SUPABASE_SERVICE_KEY in vault · **Labs shipped: 40/50 (Batches A–H ✅)** — 1 pi-li-race (68f275f5) · 2 prime-gaps (5458f5e9) · 3 andrica (0fb544d6) · 4 constellations (508fea1a) · 5 goldbach (a2b78f5c) · 6 line-walker (30b47377, R2 permalinks begin) · 7 landscape (36090e8c) · 8 orchestra (ea784574) · 9 pair-correlation (889b0304) · 10 rs-anatomy (0360275e) · 11 five-point (ae21977d, R3 tours begin) · 12 metallic (8e0c694e) · 13 pentagon (e7fec565) · 14 pentagonal (9f3afaac, incl. corpus pentagonalNumberTheorem) · 15 weyl (d004da87) · 16 gilbreath (7987f57e, R4 export begins) · 17 benford (06c122dd) · 18 ensembles (e4f78af7) · 19 contfrac (fdc767c5) · 20 solved-giants (ff223c74) · 21 mason-stothers (f4c5d67a, R5 A/B begins) · 22 zeckendorf (784bc6ab) · 23 erdos-szekeres (d1707194) · 24 cauchy-davenport (d64fbfb1, corpus EGZ theorem) · 25 machin (99e8c0fe) · 26 singular-series (40c3a2cd, R6 sonification begins; 6,461 PROVED family measured live) · 27 d5-characters (e8c103b9, 214 PROVED cluster) · 28 penrose (2fe2eb89, exact Q(√5) engine) · 29 twin-constant (172f2360, 6 certified digits w/ rigorous interval) · 30 mersenne (f0bb8974) · 31 galois (63d5b600, R7 challenges begin; 55 PROVED) · 32 prime-carnival (bd662cc5, ruthAaron_714 is a corpus theorem) · 33 franklin (ca1a987d, 8,696 partitions exhaustively verified; challenge corrected operator's wrong premise re 57) · 34 schrodinger (920a1490, Weyl family measured 706 decls/536 PROVED) · 35 golden-bridge (334da8b5) · 36 wilson (62d7ba45, R8 a11y begins; Wilson/Korselt corpus rows) · 37 reciprocity (be922d34, QR not in corpus, honest 0-adjacent) · 38 wheel (6cbe2a44, 116 PROVED Goldbach-wheel cluster) · 39 farey (b9c7f6df, 27,398 F300 pairs exact-verified) · 40 collatz (4b3c9c6d, CollatzPartial 13 rows, conjecture OPEN). CORPUS SURVEY (2026-08-09): public registry = 11,216 entries, 10,568 PROVED across 745 modules; SingularSeries.Gaps<N> = 6,322 PROVED (the Aristotle harvest crown); second half re-slated corpus-first per Chris. Registry-verbatim PROVED rows so far: 6 Andrica + 12 Admissibility + 13 Goldbach-local. Real bugs caught by self-verification: RS remainder scaling, H–L singular series q=2, Goldbach parity fold, Cramér-ratio overclaim, Andrica tail attribution.
