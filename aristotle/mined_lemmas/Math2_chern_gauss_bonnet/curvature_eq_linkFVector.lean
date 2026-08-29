import Mathlib

/-!
# Gauss–Bonnet (the `n = 1` case of Chern–Gauss–Bonnet) for the 2-torus

This file contains a *smooth* instance of the Chern–Gauss–Bonnet theorem, complementing the
combinatorial theorem `Math2.chern_gauss_bonnet` in `RequestProject.Main`.

For a closed oriented surface `M` the Chern–Gauss–Bonnet theorem reads
`∫_M K dA = 2π χ(M)`.  We prove this for the closed even-dimensional manifold
`T² = ℝ²/ℤ²` equipped with an *arbitrary* conformal metric `e^{2u}(dx² + dy²)`, where `u` is
any doubly periodic potential with enough regularity.  For such a metric the Gauss curvature
is `K = -e^{-2u} Δu` and the area density is `e^{2u}`, so the total curvature is `-∫∫ Δu`,
which vanishes by periodicity — in agreement with `χ(T²) = 0`.
-/

namespace Math2.Torus

open MeasureTheory

/-- Partial derivative in the first variable. -/

lemma curvature_eq_linkFVector (v : V) (N : ℕ) (hN : ∀ s ∈ K.link v, s.card ≤ N) :
    K.curvature v =
      ∑ k ∈ Finset.range (N + 1), (-1 : ℚ) ^ k * (K.linkFVector v k : ℚ) / ((k : ℚ) + 1) := by
  classical
  rw [K.curvature_eq_sum_link v]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (N + 1))
      (g := fun s : Finset V => s.card)
      (fun s hs => Finset.mem_range.2 (Nat.lt_succ_of_le (hN s hs)))
      (fun s : Finset V => (-1 : ℚ) ^ s.card / ((s.card : ℚ) + 1))]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.sum_congr rfl (fun s hs => by
        rw [(Finset.mem_filter.1 hs).2]), Finset.sum_const, nsmul_eq_mul]
  rw [SimplicialComplex.linkFVector]
  ring

/-- A finite simplicial complex is a *closed combinatorial `d`-manifold* (in the weak,
pseudomanifold sense) when it is pure of dimension `d` and every codimension-one face is
contained in exactly two `d`-dimensional faces. -/
structure IsClosedManifold (d : ℕ) : Prop where
  /-- The complex is nonempty. -/
  faces_nonempty : K.faces.Nonempty
  /-- No simplex has dimension larger than `d`. -/
  dim_le : ∀ s ∈ K.faces, s.card ≤ d + 1
  /-- Every simplex is contained in a `d`-dimensional one (purity). -/
  pure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = d + 1
  /-- Every codimension-one simplex lies in exactly two facets (closedness). -/
  two_facets : ∀ s ∈ K.faces, s.card = d →
    (K.faces.filter (fun t => s ⊆ t ∧ t.card = d + 1)).card = 2

end SimplicialComplex

/-! ## The Gauss–Bonnet theorem -/

open Finset in
/-- **Chern–Gauss–Bonnet (combinatorial form).**  For every finite simplicial complex —
in particular for every triangulated closed manifold of even dimension — the total
curvature equals the Euler characteristic:
`∑_{v} K(v) = χ(M)`. -/
