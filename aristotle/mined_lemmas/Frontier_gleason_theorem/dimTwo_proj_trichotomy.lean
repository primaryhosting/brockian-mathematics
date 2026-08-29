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

lemma dimTwo_proj_trichotomy {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P) :
    P = 0 ∨ P = 1 ∨ P.trace = 1 := by
  by_cases ht : P.trace = 1
  · exact Or.inr (Or.inr ht)
  have h := two_dim_cayley P
  rw [hP.2] at h
  set t : ℂ := P.trace with ht'
  set d : ℂ := P.det with hd'
  have htne : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  have h2 : (t - 1) • P = d • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [sub_smul, one_smul]
    nth_rewrite 2 [h]
    abel
  have h3 : P = ((t - 1)⁻¹ * d) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (t - 1)⁻¹ • M) h2
    simpa [smul_smul, inv_mul_cancel₀ htne] using h4
  set c : ℂ := (t - 1)⁻¹ * d with hc
  have h4 : c * c = c := by
    have h5 := hP.2
    rw [h3, smul_mul_smul_comm, one_mul] at h5
    have h6 := congrFun (congrFun h5 0) 0
    simpa using h6
  have h7 : c * (c - 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp h7 with h8 | h8
  · exact Or.inl (by rw [h3, h8, zero_smul])
  · exact Or.inr (Or.inl (by rw [h3, sub_eq_zero.mp h8, one_smul]))

/-- In dimension two, two nonzero orthogonal projections are complementary. -/
