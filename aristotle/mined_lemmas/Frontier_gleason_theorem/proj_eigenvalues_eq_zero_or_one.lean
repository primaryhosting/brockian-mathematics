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

lemma proj_eigenvalues_eq_zero_or_one {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) (i : Fin N) :
    hP.1.eigenvalues i = 0 ∨ hP.1.eigenvalues i = 1 := by
  set v : Fin N → ℂ := ⇑(hP.1.eigenvectorBasis i) with hv
  set l : ℝ := hP.1.eigenvalues i with hl
  have hvne : v ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.2 (hP.1.eigenvectorBasis.orthonormal.ne_zero i)
  have h1 : P *ᵥ v = l • v := hP.1.mulVec_eigenvectorBasis i
  have h2 : P *ᵥ (P *ᵥ v) = (l * l) • v := by
    rw [h1, Matrix.mulVec_smul, h1, smul_smul]
  have h3 : P *ᵥ (P *ᵥ v) = l • v := by
    rw [Matrix.mulVec_mulVec, hP.2, h1]
  have h5 : (l * l - l) • v = 0 := by
    rw [sub_smul, ← h2, h3, sub_self]
  have h6 : l * l - l = 0 := by
    by_contra h
    exact hvne ((smul_eq_zero.mp h5).resolve_left h)
  have h7 : l * (l - 1) = 0 := by nlinarith [h6]
  rcases mul_eq_zero.mp h7 with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- Every orthogonal projection is the sum of the rank-one projections onto the eigenvectors
belonging to the eigenvalue `1`. -/
