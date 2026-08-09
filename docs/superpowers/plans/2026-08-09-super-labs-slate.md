# Super Labs Slate — 25 Best-in-Class Labs (Phase 2)

**Directive (Chris, 2026-08-09):** "build 25 more super labs, best in class."

**Definition of a super lab** (the Zeta Observatory pattern, non-negotiable):
- `DepthShell` three-depth page: Surface (short cinematic/story), Explore (live in-browser compute via the kernel worker), Rigor (claims with register badges; PROVED claims resolve to `/verified-registry.json` by VERBATIM theorem name — omit rather than guess).
- All compute off the main thread (kernel worker tasks, new tasks get golden Vitest tests).
- ProvenanceStrip on every computed output; COMPUTATION never styled as PROVED; RH/open questions stated OPEN.
- Registered in `src/config/site-registry.ts`; routes follow the existing pattern; first-class empty/error states.
- Eyes-on verification before any publish (per standing rule).

**Execution:** batches of 2–3 labs per Lovable build message, verify each batch (kernel tests + typecheck + 0 console errors) before the next. Order below. Build 3 (Rigor layer, Task 12) ships FIRST because its ClaimRef/ProofChip primitives are reused by every lab's Rigor layer.

## Batch A — Primes & Distribution (sieve kernel)
1. **π(x) vs Li(x) Race** — prime counting vs logarithmic integral, error term live; PNT framing (PROVED in the literature ≠ in our registry — label registers honestly).
2. **Prime Gaps Explorer** — gap records, Cramér heuristic (COMPUTATION/CONJECTURE).
3. **Andrica Lab** — √p̅ₙ₊₁−√pₙ live scan; registry `Brockian.AndricaConjecture.*` PROVED pieces vs the OPEN conjecture.
4. **Twin Primes & Constellations** — twin/cousin/sexy counts vs Hardy–Littlewood (COMPUTATION; OPEN).
5. **Goldbach Comb** — partition counts g(2n) (COMPUTATION; OPEN).

## Batch B — Zeta Analytics (zeta kernel)
6. **Critical Line Walker** — long Z(t) walks, sign changes, Gram points.
7. **Zeta Landscape Explorer** — interactive pan/zoom gridAbs of the complex plane.
8. **Explicit Formula Orchestra** — per-zero contribution visual/audio, extends `explicit.ts`.
9. **Montgomery Pair Correlation** — pair correlation vs GUE prediction (COMPUTATION).
10. **Riemann–Siegel Anatomy** — main sum vs Gabcke remainder terms, live decomposition.

## Batch C — Brockian Program (spectra kernel + registry)
11. **Five-Point Alphabet Deep Lab** — charpoly walkthroughs H₁/H₂/H₃ (`Brockian.ConstellationSpectrum.*` PROVED; assembly OPEN).
12. **Metallic Means Spectra** — `Brockian.MetallicRealization.*` (PROVED) eigenvalue realizations.
13. **Pentagon Isotypic Lab** — `Brockian.PentagonIsotypic.*` adjacency eigenvalues 2cos(kπ/5), golden ratio (PROVED).
14. **Euler Pentagonal Lab** — pentagonal number theorem + partition recurrence live (`Brockian.AffineSelection.pentagonal_goldbach` and ms-euler-pentagonal if present — verify names).
15. **Weyl Scaffold Lab** — `Brockian.Weyl.*` eigenvalue-reality theorems visualized (PROVED pieces vs OPEN bridge).

## Batch D — Randomness & Structure
16. **Gilbreath Triangle Lab** — iterated prime differences (`Brockian.Gilbreath*` module; conjecture OPEN).
17. **Benford & First Digits** — leading digits of primes/zeros vs Benford (COMPUTATION).
18. **Random Matrix Ensembles** — GOE/GUE/GSE spacing side-by-side (extends spectra).
19. **Continued Fractions & Metallic Numbers** — CF expansions, Gauss–Kuzmin (COMPUTATION).
20. **Kadison–Singer / Sensitivity Lab** — the registry's `KadisonSinger`/`Sensitivity` PROVED pieces, honest scope.

## Batch E — Classical Named Theorems (registry `ms-*` PROVED set)
21. **Mason–Stothers Lab** — polynomial abc, interactive examples.
22. **Zeckendorf Lab** — Fibonacci representation encoder.
23. **Erdős–Szekeres Lab** — monotone subsequence finder.
24. **Cauchy–Davenport Lab** — sumsets mod p, interactive.
25. **Machin π Lab** — Machin-type formulas computing π digits live.

For every registry citation above: the build message must instruct the Lovable agent to resolve the exact theorem name from `/public/verified-registry.json` and copy it verbatim; if absent, the claim is omitted or downgraded — never invented.

**Status log**
- [ ] Task 12 (Rigor primitives) — prerequisite
- [ ] Batch A · [ ] Batch B · [ ] Batch C · [ ] Batch D · [ ] Batch E
