# Matrix reindexing closed; open path-block identification

The `SimpleGraph.adjMatrix` to connected-component block-diagonal step is now AXLE-verified in
`Brockian.GraphComponentMatrix` and specialized to the twin graph in
`Brockian.ConstellationGateClose`. This document now records the smaller remaining step.

## Goal

Transport the exact spectrum from the *assembled* block operator (already proved) to the *graph's own*
adjacency operator. Concretely, for `G := SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)`
with `M` squarefree, `Nat.Coprime 3 M`, `5 ∣ M`, `1 < M`:

```lean
-- The graph Hamiltonian: H_G := 2 • 1 − adjMatrix ℝ G, over the admissible-vertex Fintype.
theorem graph_hamiltonian_spectrum_subset (x : ℝ) :
    (2 • (1 : Matrix _ _ ℝ) - SimpleGraph.adjMatrix ℝ G).charpoly.eval x = 0 →
      x ∈ ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set ℝ)
```

The implication is the correct unconditional Route C target. An `↔` requires occurrence
hypotheses: a `P₂` component must occur for `1,3`, and a `P₃` component must occur for
`2 ± sqrt 2`. The boundary case `M = 5` satisfies the displayed modulus hypotheses but its
twin-admissible graph is just `P₃`, so `1` and `3` are not eigenvalues. The exact charpoly theorem
below records zero multiplicities correctly and is therefore the preferred full statement.

and, with the component counts `n₁, n₂, n₃` (from `ConstellationCounts`: `n₃ = T`, `n₂ = E − 2T`,
`n₁ = V − 2E + T`, where `V = ∏(p−2)`, `E = ∏(p−4)`, `T = ∏(p−6)`), the multiplicity form:

```lean
theorem graph_hamiltonian_charpoly :
    (2 • (1 : Matrix _ _ ℝ) - SimpleGraph.adjMatrix ℝ G).charpoly
      = (X - C 2) ^ n₁ * ((X - C 1) * (X - C 3)) ^ n₂ * ((X - C 2) * (X ^ 2 - C 4 * X + C 2)) ^ n₃
```

## Matrix bridge now proved

The following statements are AXLE-verified at Lean 4.32:

- `GraphComponentMatrix.componentEquiv`: vertices are equivalent to the sigma of the fibers of
  `G.connectedComponentMk`.
- `GraphComponentMatrix.reindex_componentEquiv_eq_blockDiagonal'`: every matrix with zero
  cross-component entries reindexes to `Matrix.blockDiagonal'`.
- `GraphComponentMatrix.adjMatrix_reindex_components`: the graph adjacency matrix reindexes to the
  dependent block diagonal of the actual induced component adjacency matrices.
- `GraphComponentMatrix.charpoly_eq_prod_componentBlocks`: any such matrix has charpoly equal to the
  product of its component-block charpolys, using Mathlib's existing
  `Matrix.BlockTriangular.charpoly` theorem.
- `ConstellationGateClose.graph_hamiltonian_reindex_components` and
  `graph_hamiltonian_charpoly_components`: the requested identities for the actual twin graph
  Hamiltonian `2I-A`.

## Other proved prerequisites

- `ConstellationGraphAcyclic.twin_admissible_induced_acyclic` — `G.IsAcyclic`.
- `ConstellationPaths.induced_degree_le_two` — every vertex has degree ≤ 2.
- `ConstellationPaths.forest_of_paths` — the formal statement
  `G.IsAcyclic ∧ ∀ v, G.degree v ≤ 2`; identifying each component with a concrete `pathGraph` is
  part of the remaining bridge.
- `ConstellationPaths.no_four_admissible_run` — no 4 vertices in a `+3` progression (components ≤ 3
  vertices), so every component is `P₁`, `P₂`, or `P₃`.
- `ConstellationAdjBridge.G_embeds_intLine` — the map `pos a = (3⁻¹·a).val : ℤ` is a full
  `SimpleGraph.Embedding` (induced, both directions) of `G` into the integer line graph. Packaging
  the resulting component intervals as explicit equivalences is part of the remaining bridge.
- `ConstellationSpectrum` / `ConstellationBlockSum` / `ConstellationGlobalSpectrum` — the path
  Hamiltonians `H₁,H₂,H₃`, their exact charpolys, the direct-sum charpoly law
  `charpoly_fromBlocks_zero`, and `H123_spectrum` (the assembled block operator's spectrum is exactly
  the five-point alphabet).

The matrix factorization is therefore no longer the blocker.

## The precise remaining gap

For each `c : G.ConnectedComponent`:

1. Prove `Fintype.card (ComponentFiber G c) ∈ {1,2,3}` from acyclicity, degree at most two, the
   no-four-run theorem, and `G_embeds_intLine`.
2. Construct a graph equivalence from `componentGraph G c` to the matching path graph.
3. Transport its shifted adjacency matrix to `H₁`, `H₂`, or `H₃` and identify its charpoly factor.
4. Prove that the numbers of components of each size are the arithmetic `n₁,n₂,n₃`, then regroup
   `graph_hamiltonian_charpoly_components` into `pathBlockCharpoly n₁ n₂ n₃`.

The shortest route is through the integer-line embedding: attach to each component the minimum and
maximum image positions, prove every intermediate integer position belongs to the image, and use the
run cap to bound the interval cardinality by three. This produces the explicit path ordering needed
for the graph equivalence and avoids a second matrix decomposition.

## Definition of done

`graph_hamiltonian_spectrum_subset` or the full multiplicity-aware `graph_hamiltonian_charpoly`
proved from `graph_hamiltonian_charpoly_components`, AXLE-verified at Lean 4.32, and root-integrated.
Reminder: this remains a structural/finite result; it is **not** a proof of twin-prime infinitude.
