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

lemma coeff_eigen {v : ZMod 17 → ℂ} {μ : ℂ} (hv : C17adj *ᵥ v = μ • v) (m : ZMod 17) :
    μ * coeff v m = lam m * coeff v m := by
  have hstep : ∀ j : ZMod 17, μ * v j = v (j - 1) + v (j + 1) := by
    intro j
    have := congrFun hv j
    rw [mulVec_C17adj] at this
    simpa [mul_comm] using this.symm
  have hL : μ * coeff v m = ∑ j : ZMod 17, ee (-(m * j)) * (v (j - 1) + v (j + 1)) := by
    rw [coeff, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hstep j]; ring
  have hA : ∑ j : ZMod 17, ee (-(m * j)) * v (j - 1)
      = ∑ j : ZMod 17, (ee (-(m * j)) * ee (-m)) * v j := by
    rw [← sum_shift (fun j => ee (-(m * j)) * v (j - 1))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have harg : -(m * (j + 1)) = -(m * j) + -m := by ring
    rw [harg, ee_add]
    congr 2
    ring
  have hB : ∑ j : ZMod 17, ee (-(m * j)) * v (j + 1)
      = ∑ j : ZMod 17, (ee (-(m * j)) * ee m) * v j := by
    rw [← sum_shift (fun j => (ee (-(m * j)) * ee m) * v j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have harg : -(m * (j + 1)) + m = -(m * j) := by ring
    rw [← harg, ee_add]
  rw [hL]
  simp only [mul_add]
  rw [Finset.sum_add_distrib, hA, hB, coeff, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← ee_add_ee_neg m]
  ring

