-- Ray Indicator Eq Char Sum (see module docstring below; `import` must come first in Lean 4)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`, `e a = ω ^ a`. -/
noncomputable def e (a : ZMod 5) : ℂ := omega ^ a.val

lemma omega_primitive : IsPrimitiveRoot omega 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega, mul_comm, mul_assoc, mul_left_comm] using h

/-- The full character sum vanishes: `∑ a, e a = 0`. -/
lemma sum_e : ∑ a : ZMod 5, e a = 0 := by
  have h := omega_primitive.geom_sum_eq_zero (by norm_num)
  rw [← h, show (∑ a : ZMod 5, e a) = ∑ a : Fin 5, omega ^ (a : ℕ) from rfl]
  simp [Fin.sum_univ_five, Finset.sum_range_succ]

/-- Orthogonality of the additive characters on `ZMod 5`. -/
lemma sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hb : b = 0
  · simp [hb, e]
  · rw [if_neg hb, ← sum_e]
    exact Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ (fun _ => rfl)

/-- Indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Spectral decomposition of the ray indicator into additive characters. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  have h : ∀ a : ZMod 5, e (a * ((n : ZMod 5) - r)) = e (((n : ZMod 5) - r) * a) := by
    intro a; rw [mul_comm]
  simp_rw [h, sum_e_mul, sub_eq_zero, rayIndicator]
  split <;> norm_num

#print axioms Brockian.Characters5.rayIndicator_eq_charSum

end Brockian.Characters5

