# Grinberg graph-theory reference spine

Date: 2026-08-23

Source: Darij Grinberg, *An introduction to graph theory*, arXiv:2308.04512v3,
version June 7, 2025, CC0-1.0

Exact source manifest:
`provenance/reference-spines/grinberg-graph-theory-v3.yaml`

## Outcome

The first source-backed slice is integrated without duplicating the repository's existing
`Aut(C5) ~= D5` or cycle-spectrum work. It adds the missing concrete adjacency/walk layer:

| Result | Lean declaration | Status | Provenance class |
|---|---|---|---|
| Every vertex of `C5` has degree 2 | `Brockian.GrinbergC5Reference.c5_degree_eq_two` | Lean source integrated; AXLE pending | `CLASSICAL_REFERENCE` |
| `C5` has 5 edges | `Brockian.GrinbergC5Reference.c5_edge_count_eq_five` | Lean source integrated; AXLE pending | `CLASSICAL_REFERENCE` |
| `(A^n)[u,v]` counts length-`n` walks | `Brockian.GrinbergC5Reference.c5_adjacency_power_counts_walks` | Lean source integrated; AXLE pending | `CLASSICAL_REFERENCE` |
| `trace(A^n)` counts based closed walks | `Brockian.GrinbergC5Reference.c5_adjacency_trace_counts_closed_walks` | Lean source integrated; AXLE pending | `CLASSICAL_REFERENCE` |
| `trace(A^2) = 10` | `Brockian.GrinbergC5Reference.c5_adjacency_trace_sq_eq_ten` | Lean source integrated; AXLE pending | `CLASSICAL_REFERENCE` |
| There are 10 based closed 2-walks | `Brockian.GrinbergC5Reference.c5_closed_walks_length_two_eq_ten` | Lean source integrated; AXLE pending | `CLASSICAL_REFERENCE` |

“Lean source integrated; AXLE pending” is intentionally not `PROVED` registry status. The
source is root-imported and contains no `sorry`, `admit`, or `native_decide`, but the corpus
requires a separate AXLE attestation before registry promotion.

## Exact source map

| Printed pages | Source anchor | Repository treatment |
|---|---|---|
| 6 | CC0 dedication/license | License and exact PDF SHA-256 recorded in the manifest |
| 29–30 | Definition 2.6.3; rotations, reflections, and `Aut(Cn) = Dn` for `n > 2` | Reuse `Brockian.Automorphism.C5` and `Brockian.Automorphism.Full.autEquivDihedral`; no duplicate theorem |
| 121 | Theorem 4.5.10, adjacency powers count walks | New `C5` specialization and closed-walk trace consequences |
| 167–168 | Example 5.4.4, `Cn` has exactly `n` spanning trees | Queued; no declaration claimed |
| 208 | Example 5.8.6, the directed cycle has one rooted spanning arborescence | Queued; no declaration claimed |
| 252 | Theorem 5.15.1, undirected Matrix-Tree Theorem | Queued; no declaration claimed |
| 280 | Theorem 5.19.2, weighted Matrix-Tree Theorem | Queued; no declaration claimed |

## Classical results versus bridge work

The machine-readable tags have deliberately different meanings:

- `CLASSICAL_REFERENCE`: externally sourced mathematics, excluded from novelty counting.
- `BROCKIAN_BRIDGE`: formal wiring from classical graph theory into existing phase-depth,
  transfer, representation, or spectral modules; also excluded from novelty counting.
- `BROCKIAN_RESULT`: a mathematical novelty assertion requiring separate review. No slice
  in this ingestion is tagged this way.
- `EMPIRICAL_COMPUTATION`: a finite experiment or analysis, never promoted to `PROVED`.

The existing bridge is explicit rather than rhetorical:

- `Brockian.PhaseDepthClassification.cohomologous_iff_totalDepth_eq` gives the complete
  gauge classification on one directed pentagonal cycle.
- `Brockian.PhaseDepthD5.d5_covariance` gives the rotation/reflection covariance of total
  depth.
- `Brockian.PhaseDepthTraceMatrix.trace_transferMatrix_pow` makes the transfer trace a
  literal periodic-point count.
- `Brockian.CycleSpectrumFamily.golden_in_C5` is a downstream adjacency-spectrum fact;
  its golden value is classical and is not relabeled as a Brockian discovery.

## Boundary that must not be crossed silently

The weighted Matrix-Tree Theorem is not a gauge/cohomology classification theorem.
Grinberg's directed Laplacian uses outdegree minus adjacency, and its minor counts
arborescences rooted to the selected vertex. A future phase-depth bridge must encode those
sign and root conventions explicitly; a superficial “determinant equals holonomy” analogy
is not an admissible theorem-ingestion step.

Likewise, the arithmetic-discrimination report at
`docs/phase-depth/2026-08-23-arithmetic-discrimination-experiment.md` remains tagged
`EMPIRICAL_COMPUTATION`: its observed percentages do not enter the theorem registry or the
novelty ledger.

## Enforcement

`scripts/validate_reference_spines.py` is a blocking provenance firewall. It checks that:

1. classical, bridge, and empirical slices cannot opt into the novelty ledger;
2. `registry_verified` declarations resolve to green registry entries;
3. pending Lean declarations exist in their stated source files but are not promoted;
4. queued slices claim no declarations; and
5. empirical artifacts exist and claim no Lean declarations.

The next formal slice is `cycle-spanning-tree-count`, followed by the directed-cycle root
convention. Matrix-Tree interfaces come only after those definitions are stable.
