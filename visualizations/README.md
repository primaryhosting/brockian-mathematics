# Visualizations

Standalone visualization components kept on hand for the Brockian program.
Convention: Chris-provided originals are archived verbatim; corrections live in
`*.fixed.jsx` copies (no-delete rule). Review findings of 2026-08-27 are
summarized per component below; the three lemma candidates the reviews surfaced
are queued in `research/manual-targets.json`.

## BrockianVisualizer.jsx

Provided by Chris, 2026-08-27, archived verbatim. A React/SVG 3D helix
visualizer of the Brockian pentagonal number line: integers spiral outward with
vertex assignment `|n| mod 5 → {A, B, C, D, E}` at pentagon angles
(90°/162°/234°/306°/18°), radius `|n|`, height `n`. Overlay modes highlight
primes, triangular, pentagonal, and Fibonacci numbers per vertex, with
rotation/elevation/count-by controls.

Relationship to the live site: the flagship `/labs/number-line` lab on
torus.riemannlab.com covers this territory in production form; this component
is the compact, dependency-free (React + Tailwind only) reference version —
useful for embedding in writeups, the book, or quick demos.

Known limitations (archived as-is, fix only in a copy):
- `isTriangular` / `isPentagonal` use exact float equality (`k === Math.floor(k)`)
  — misclassifies at larger `n`; an integer-arithmetic check is the fix.
- `isFibonacci` is a fixed set up to 89, so only valid for `|n| ≤ maxNumber ≈ 90`.
- `maxNumber` and `showGrid` state exist but have no UI control;
  `highlightedVertex` is set but unused.
- "Show Connections" draws lines in depth-sorted order, not numeric order, so
  connection lines change topology as the view rotates.
- `Math.abs(n) % 5` is NOT the residue of n mod 5 — it mirror-folds negatives
  (−1 shows on vertex B; in ZMod 5, −1 ≡ 4 belongs on E), accidentally
  quotienting by the D5 reflection instead of displaying it.

## BrockianVisualizer.fixed.jsx

Corrected copy: true ZMod 5 residue (negation now displays as the D5
reflection, matching the proved autEquivDihedral symmetry), numeric-order
connections with depth used only for paint order, integer-exact
triangular/pentagonal predicates, exact Fibonacci test (5n²±4 square),
adaptive scale, maxNumber slider + showGrid checkbox wired, hover highlights
the whole residue class. Future (deliberate, per review): a gap-patterns mode
citing the q=5→3 admissibility law and a D5 symmetry toggle citing
aut_card_eq_ten — each dropdown entry should cite a registry theorem before
this ships as a lab.

## BrockianSpiralPrimordialPrimes.jsx

Provided by Chris, 2026-08-27, archived verbatim. Prime-constellation plot on
mod-5 rays. **Fatal bug (theorem-diagnosed):** the searched offset pattern
{0,1,3,5,9,11,15,17,21} covers both residues mod 2 — inadmissible by the
corpus's own AdmissibilityHLCriterion — so the search below 10⁶ returns only
the seed tuple at 2 and the plot is a single dot. Also: θ takes 5 discrete
values (4 populated rays, not a spiral), `getColor` indexes by leading digit,
and the 10⁶ sieve blocks the mount render.

## BrockianConstellations.fixed.jsx

Corrected replacement. Uses genuinely admissible patterns checked by the same
ν(p) < p criterion the corpus formalizes; defaults to constellations actually
visible below the sieve limit — note the densest admissible 8-tuple
[0,2,6,8,12,18,20,26] has its second occurrence ≈15.76M, so an 8-tuple demo
below 10⁶ would still render one dot. The mod-5 ray layout is now the point:
twin pairs populate exactly 3 of 5 residue classes and quadruplets exactly 1 —
the q − ν(q) law, displayed with the populated-residue count in the panel.
Golden-angle spiral layout as the alternative view; sieve memoized.
