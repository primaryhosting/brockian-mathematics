import Mathlib

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

/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` into `ℂ`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  unfold omega
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  convert this using 2

/-- The full character sum over `ZMod 5` vanishes. -/
theorem sum_e_eq_zero : ∑ b : ZMod 5, e b = 0 := by
  have h := isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)
  rw [show (∑ b : ZMod 5, e b) = ∑ b : ZMod 5, omega ^ b.val from rfl, ← h]
  exact Finset.sum_nbij (fun b => b.val)
    (by simp [ZMod.val_lt])
    (fun a _ b _ hab => ZMod.val_injective _ hab)
    (fun k hk => by
      simp only [Finset.coe_range, Set.mem_Iio] at hk
      exact ⟨(k : ZMod 5), by simp, by simp [ZMod.val_natCast_of_lt hk]⟩)
    (fun _ _ => rfl)

/-- Orthogonality: the character sum detects whether `x = 0`. -/
theorem rayIndicator_eq_charSum (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · subst hx; simp [e]
  · rw [if_neg hx]
    have hshift : ∑ a : ZMod 5, e (a * x) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulRight₀ x hx) _ _ (fun _ => rfl)
    rw [hshift]
    exact sum_e_eq_zero

/-- The number of elements of `S` lying on the ray `r` mod `5`. -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ := (S.filter fun n : ℕ => (n : ZMod 5) = r).card

/-- Ray-count identity: the number of elements of `S` on ray `r` equals
`(1/5) ∑_{a : ZMod 5} ∑_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ) = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  rw [raySum, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [rayIndicator_eq_charSum ((n : ZMod 5) - r)]
  by_cases h : (n : ZMod 5) = r <;> simp [h, sub_eq_zero]

end Characters5
end Brockian

