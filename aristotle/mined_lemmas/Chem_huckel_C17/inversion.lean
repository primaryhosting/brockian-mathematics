/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma inversion (v : ZMod 17 → ℂ) (i : ZMod 17) :
    ∑ m : ZMod 17, ee (m * i) * coeff v m = 17 * v i := by
  have h1 : ∑ m : ZMod 17, ee (m * i) * coeff v m
      = ∑ j : ZMod 17, (∑ m : ZMod 17, ee (m * (i - j))) * v j := by
    simp only [coeff, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun m _ => ?_))
    have harg : m * (i - j) = m * i + -(m * j) := by ring
    rw [harg, ee_add]
    ring
  rw [h1]
  have h2 : ∀ j : ZMod 17, (∑ m : ZMod 17, ee (m * (i - j))) * v j
      = if j = i then 17 * v i else 0 := by
    intro j
    rw [sum_ee_mul]
    by_cases hj : j = i
    · subst hj; simp
    · have : i - j ≠ 0 := fun h => hj (by rw [← sub_eq_zero]; rw [← neg_eq_zero]; rw [← h]; ring)
      simp [this, hj]
  rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_ite_eq']
  simp

/-! ### Main theorem -/

/-- **Hückel theory for the cycle `C₁₇`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₇` if and only if `μ = 2 cos (2πk/17)` for some
`k ∈ {0, 1, …, 16}`. -/
