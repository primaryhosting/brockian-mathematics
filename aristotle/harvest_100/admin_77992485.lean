import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` associated with `omega`. -/
noncomputable def e (a : ZMod 5) : ℂ := omega ^ a.val

/-- The indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega, mul_comm, mul_assoc, mul_left_comm] using h

theorem e_zero : e 0 = 1 := by
  simp [e]

/-- The full character sum vanishes. -/
theorem sum_e_univ : ∑ c : ZMod 5, e c = 0 := by
  have h : ∑ i ∈ Finset.range 5, omega ^ i = 0 :=
    omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one] at h
  show ∑ c : Fin 5, e c = 0
  rw [Fin.sum_univ_five]
  simpa [e, ZMod.val] using h

/-- Orthogonality relation for the character `e`. -/
theorem sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  by_cases hb : b = 0
  · subst hb
    simp [e_zero]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hb]
    have hbij : ∑ a : ZMod 5, e (b * a) = ∑ c : ZMod 5, e c := by
      refine Fintype.sum_bijective (fun a => b * a) ?_ _ _ (fun a => rfl)
      exact mulLeft_bijective₀ b hb
    rw [hbij, sum_e_univ]

/-- Indicator decomposition: the ray indicator `𝟙[n ≡ r (mod 5)]` equals
`(1/5) Σ_{a : ZMod 5} e (a * (n - r))`. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hbdef
  have hcomm : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [mul_comm]
  rw [hcomm, sum_e_mul b]
  have hb : b = 0 ↔ (n : ZMod 5) = r := by
    rw [hbdef, sub_eq_zero]
  unfold rayIndicator
  by_cases h : (n : ZMod 5) = r
  · rw [if_pos h, if_pos (hb.mpr h)]
    norm_num
  · rw [if_neg h, if_neg (fun hc => h (hb.mp hc))]
    norm_num

end Characters5
end Brockian

