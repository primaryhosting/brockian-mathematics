import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` on vertices `0,1,2,3,4`:
vertices `i` and `j` are adjacent iff `j ≡ i + 1` or `i ≡ j + 1` modulo `5`. -/

lemma char_root_iff (m : ℂ) :
    m ^ 5 - 5 * m ^ 3 + 5 * m - 2 = 0 ↔
      m = 2 ∨ m = (-1 + ((√5 : ℝ) : ℂ)) / 2 ∨ m = (-1 - ((√5 : ℝ) : ℂ)) / 2 := by
  have hfac : m ^ 5 - 5 * m ^ 3 + 5 * m - 2 =
      (m - 2) * ((m - (-1 + ((√5 : ℝ) : ℂ)) / 2) * (m - (-1 - ((√5 : ℝ) : ℂ)) / 2)) ^ 2 := by
    linear_combination ((m - 2) * (2 * (m ^ 2 + m - 1) + (5 - ((√5 : ℝ) : ℂ) ^ 2) / 4) / 4) *
      sqrt_five_sq
  rw [hfac]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      rcases mul_eq_zero.mp this with h3 | h4
      · exact Or.inr (Or.inl (sub_eq_zero.mp h3))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h4))
  · rintro (rfl | rfl | rfl) <;> ring

/-! ### Main theorem -/

/-- **Hückel theory for the cyclopentadienyl ring (C₅).**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₅`
(that is, `A *ᵥ v = μ • v` for some nonzero vector `v`) if and only if
`μ = 2 cos (2πk/5)` for some `k ∈ {0,1,2,3,4}`. -/
