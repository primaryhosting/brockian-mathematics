# Open problem: the `adjMatrix` → block-diagonal reindexing step

*The single remaining step to fully close the constellation-sieve spectral gate. This is a
**formalization** problem, not a mathematical one — the mathematics is immediate; the Mathlib
`SimpleGraph.adjMatrix` ⇄ `Matrix` block machinery is what's missing.*

## Goal

Transport the exact spectrum from the *assembled* block operator (already proved) to the *graph's own*
adjacency operator. Concretely, for `G := SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)`
with `M` squarefree, `Nat.Coprime 3 M`, `5 ∣ M`, `1 < M`:

```lean
-- The graph Hamiltonian: H_G := 2 • 1 − adjMatrix ℝ G, over the admissible-vertex Fintype.
theorem graph_hamiltonian_spectrum (x : ℝ) :
    (2 • (1 : Matrix _ _ ℝ) - SimpleGraph.adjMatrix ℝ G).charpoly.eval x = 0 ↔
      x ∈ ({2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2} : Set ℝ)
```

and, with the component counts `n₁, n₂, n₃` (from `ConstellationCounts`: `n₃ = T`, `n₂ = E − 2T`,
`n₁ = V − 2E + T`, where `V = ∏(p−2)`, `E = ∏(p−4)`, `T = ∏(p−6)`), the multiplicity form:

```lean
theorem graph_hamiltonian_charpoly :
    (2 • (1 : Matrix _ _ ℝ) - SimpleGraph.adjMatrix ℝ G).charpoly
      = (X - C 2) ^ n₁ * ((X - C 1) * (X - C 3)) ^ n₂ * ((X - C 2) * (X ^ 2 - C 4 * X + C 2)) ^ n₃
```

## What is already proved (the prerequisites — all AXLE-verified @lean-4.32.0, axiom-clean)

- `ConstellationGraphAcyclic.twin_admissible_induced_acyclic` — `G.IsAcyclic`.
- `ConstellationPaths.induced_degree_le_two` — every vertex has degree ≤ 2.
- `ConstellationPaths.forest_of_paths` — `G.IsAcyclic ∧ ∀ v, G.degree v ≤ 2` (disjoint union of paths).
- `ConstellationPaths.no_four_admissible_run` — no 4 vertices in a `+3` progression (components ≤ 3
  vertices), so every component is `P₁`, `P₂`, or `P₃`.
- `ConstellationAdjBridge.G_embeds_intLine` — the map `pos a = (3⁻¹·a).val : ℤ` is a full
  `SimpleGraph.Embedding` (induced, both directions) of `G` into the integer line graph; hence **each
  connected component is a contiguous integer interval** (a genuine path of ≤ 3 vertices).
- `ConstellationSpectrum` / `ConstellationBlockSum` / `ConstellationGlobalSpectrum` — the path
  Hamiltonians `H₁,H₂,H₃`, their exact charpolys, the direct-sum charpoly law
  `charpoly_fromBlocks_zero`, and `H123_spectrum` (the assembled block operator's spectrum is exactly
  the five-point alphabet).

So: the graph **is** a disjoint union of path components, each an integer interval; the spectrum of a
disjoint union of paths **is** the union of the path spectra; and those are `{2−√2,1,2,3,2+√2}`. All
that remains is to say this at the level of `Matrix.charpoly`.

## The precise gap

Mathlib (as of this toolchain) has no lemma giving a **block-diagonal decomposition of an adjacency
matrix by connected components**. Needed, roughly:

1. A `Fintype`-reindexing `e : (admissible vertices) ≃ Σ (c : G.ConnectedComponent), (c's vertices)`
   grouping each component's vertices contiguously — the `pos`-order from `G_embeds_intLine` supplies the
   ordering; what's missing is packaging it as an equivalence that Mathlib's `Matrix.reindex` accepts.
2. `SimpleGraph.adjMatrix` reindexed by `e` is **block-diagonal**: no edge crosses components (true by
   definition of connected component). A lemma of the form
   `(adjMatrix R G).reindex e e = Matrix.blockDiagonal (fun c => adjMatrix R (G.induce c))` or the
   `Σ`-typed analogue.
3. `Matrix.charpoly_reindex` (charpoly invariant under simultaneous row/col reindex — similarity) and a
   `charpoly` of a `Σ`-indexed block-diagonal = `∏` of block charpolys (Mathlib has
   `Matrix.charpoly_fromBlocks_zero₂₁` for the binary case; the `Σ`/`blockDiagonal` version over a
   variable index set is what's needed, or fold the binary case over the finite component set).
4. Each block is the adjacency matrix of a `P_k` (`k ≤ 3`), whose Hamiltonian charpoly is one of the
   three factors from `ConstellationSpectrum` (identify `adjMatrix (pathGraph k)` with `Hₖ` up to the
   `2•I − ·` shift and a permutation within the block).

## Suggested attack (for a future session)

- **Route A (blockDiagonal over `Σ`).** Prove step 2 as `adjMatrix.reindex = blockDiagonal (component
  blocks)` using `SimpleGraph.ConnectedComponent` and that adjacency respects components; then a
  `charpoly (blockDiagonal M) = ∏ i, (M i).charpoly` lemma (prove it if absent, by induction on the
  index Fintype via `charpoly_fromBlocks_zero₂₁`). This is the cleanest if the reindexing equivalence
  can be built.
- **Route B (transport via the embedding).** Use `G_embeds_intLine` to identify `G` with an induced
  subgraph of `intLine` on a finite set of integers that is a disjoint union of intervals; compute the
  adjacency/Hamiltonian charpoly of a "union of integer intervals" subgraph directly (a tridiagonal /
  path-block matrix), leveraging that `pos` already orders the vertices. This sidesteps
  `ConnectedComponent` in favour of the concrete interval structure already proved.
- **Route C (eigenvalue containment, weaker but sufficient for the alphabet).** Skip the exact charpoly;
  prove only that every eigenvalue of `2•I − adjMatrix G` lies in the five-point set, by showing an
  eigenvector restricted to any component is an eigenvector of that component's path Hamiltonian. This
  closes the *spectral alphabet* claim (spectrum ⊆ `{2−√2,1,2,3,2+√2}`) without the full multiplicities.

Route C is the smallest honest close of "the graph operator's spectrum is the five-point alphabet";
Route A/B additionally recover the exact multiplicities `n₁,n₂,n₃`.

## Definition of done

`graph_hamiltonian_spectrum` (Route C minimum) or `graph_hamiltonian_charpoly` (Route A/B, full) proved,
AXLE-verified @lean-4.32.0, axiom-clean, integrated as `Brockian/ConstellationGateClose.lean` — at which
point the constellation-sieve spectral gate is **fully closed** and the paper's §9 open note is removed.
Reminder: this remains a structural/finite result; it is **not** a proof of twin-prime infinitude.
