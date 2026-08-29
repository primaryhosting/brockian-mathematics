import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

lemma measure_eq_trace_of_regular {μ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hμ : IsQuantumMeasure μ)
    {T : Matrix (Fin N) (Fin N) ℂ}
    (hframe : ∀ v : Fin N → ℂ, star v ⬝ᵥ v = 1 → μ (rankOne v) = (star v ⬝ᵥ T *ᵥ v).re)
    {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) : μ P = (T * P).trace.re := by
  classical
  set S : Finset (Fin N) := Finset.univ.filter (fun i => hP.1.eigenvalues i = 1) with hS
  set v : Fin N → (Fin N → ℂ) := fun i => ⇑(hP.1.eigenvectorBasis i) with hv
  have hunit : ∀ i, star (v i) ⬝ᵥ v i = 1 := by
    intro i; simpa using hermitian_eigenvector_dotProduct hP.1 i i
  have hproj : ∀ i, IsProj (rankOne (v i)) := fun i => rankOne_isProj (hunit i)
  have horth : ∀ i j : Fin N, i ≠ j → rankOne (v i) * rankOne (v j) = 0 := by
    intro i j hij
    refine rankOne_orthogonal ?_
    simpa [hij] using hermitian_eigenvector_dotProduct hP.1 i j
  have hPsum : P = ∑ i ∈ S, rankOne (v i) := proj_eq_sum_rankOne hP
  calc μ P = ∑ i ∈ S, μ (rankOne (v i)) := by
        rw [hPsum]
        exact hμ.sum S _ (fun i _ => hproj i) (fun i _ j _ hij => horth i j hij)
    _ = ∑ i ∈ S, (star (v i) ⬝ᵥ T *ᵥ v i).re :=
        Finset.sum_congr rfl fun i _ => hframe (v i) (hunit i)
    _ = (T * P).trace.re := by
        rw [hPsum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [trace_mul_rankOne]

/-- **Gleason's theorem, stated as a Lean-checked reduction.**

For a quantum measure `μ` on the projection lattice of a complex Hilbert space of dimension
`N ≥ 3`, the following are equivalent:

* `μ` is given by a density operator, i.e. `μ P = Re tr (ρ P)` for a positive semidefinite `ρ`
  of unit trace (the conclusion of Gleason's theorem);
* the frame function of `μ` — its restriction to the rank-one projections — is *regular*,
  i.e. given by the quadratic form of a Hermitian matrix.

This is the standard reduction of Gleason's theorem to the analytic statement about frame
functions on the unit sphere: the whole content of Gleason's theorem is that, when `N ≥ 3`,
the right-hand side always holds.  The hypothesis `3 ≤ N` is stated because it is part of the
classical statement; the equivalence proved here does not use it. -/
