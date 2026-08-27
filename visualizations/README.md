# Visualizations

Standalone visualization components kept on hand for the Brockian program.

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
