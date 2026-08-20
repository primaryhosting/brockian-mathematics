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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` sending `a` to `ω ^ a`. -/
noncomputable def e (a : ZMod 5) : ℂ := ω ^ a.val

/-- `ω` is a primitive fifth root of unity. -/
lemma omega_isPrimitiveRoot : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [ω] using h

/-- The full character sum vanishes. -/
lemma sum_e_univ : ∑ a : ZMod 5, e a = 0 := by
  have h : ∑ i ∈ Finset.range 5, ω ^ i = 0 :=
    omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  have h2 : ∑ a : ZMod 5, e a = ∑ i ∈ Finset.range 5, ω ^ i := by
    show ∑ a : Fin 5, ω ^ (ZMod.val (n := 5) a) = _
    simp [Fin.sum_univ_five, Finset.sum_range_succ, ZMod.val]
  rw [h2, h]

/-- Orthogonality relation for the character `e`. -/
lemma sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  by_cases hb : b = 0
  · subst hb
    simp [e, ω]
  · rw [if_neg hb]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : ∑ a : ZMod 5, e (b * a) = ∑ a : ZMod 5, e a :=
      Fintype.sum_bijective (fun a => b * a) (mulLeft_bijective₀ b hb) _ _ (fun _ => rfl)
    rw [this, sum_e_univ]

/-- The indicator function of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Indicator decomposition: the ray indicator `𝟙[n ≡ r (mod 5)]` equals
`(1/5) Σ_{a : ZMod 5} e (a * (n - r))`. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hbdef
  have hcomm : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [mul_comm]
  rw [hcomm, sum_e_mul]
  by_cases h : (n : ZMod 5) = r
  · have hb : b = 0 := by rw [hbdef, sub_eq_zero]; exact h
    rw [if_pos hb, rayIndicator, if_pos h]
    norm_num
  · have hb : b ≠ 0 := by
      intro hb0
      exact h (by rwa [hbdef, sub_eq_zero] at hb0)
    rw [if_neg hb, rayIndicator, if_neg h]
    norm_num

end Characters5
end Brockian

