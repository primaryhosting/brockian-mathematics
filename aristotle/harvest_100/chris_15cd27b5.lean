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

namespace Brockian
namespace Characters5

open Complex Finset

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` sending `x` to `omega ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

/-- The number of elements of `S` lying on the ray `r` modulo `5`. -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ := (S.filter fun n : ℕ => ((n : ZMod 5) = r)).card

lemma omega_isPrimitiveRoot : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma e_zero : e 0 = 1 := by simp [e]

/-- The full character sum over `ZMod 5` vanishes. -/
lemma sum_e : ∑ b : ZMod 5, e b = 0 := by
  have h : ∑ b : ZMod 5, e b = ∑ i ∈ Finset.range 5, omega ^ i := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    show ∑ b : Fin 5, omega ^ (b.val) = _
    rw [Fin.sum_univ_five]
    rfl
  rw [h]
  exact omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)

/-- Orthogonality: the character sum detects whether `x = 0`. -/
lemma sum_e_mul (x : ZMod 5) : ∑ a : ZMod 5, e (a * x) = if x = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · subst hx
    simp [e_zero]
  · rw [if_neg hx]
    have : ∑ a : ZMod 5, e (a * x) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulRight₀ x hx) _ _ (fun a => rfl)
    rw [this, sum_e]

/-- The indicator of the ray `r` as a character sum. -/
lemma rayIndicator_eq_charSum (n : ℕ) (r : ZMod 5) :
    (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  rw [sum_e_mul]
  by_cases h : (n : ZMod 5) = r
  · rw [if_pos h, if_pos (by rw [h, sub_self])]
    norm_num
  · rw [if_neg h, if_neg (fun hc => h (by rwa [sub_eq_zero] at hc))]
    ring

/-- Ray-count identity: the number of elements of `S` on the ray `r` equals
`(1/5) Σ_{a} Σ_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  have hcard : ((raySum S r : ℕ) : ℂ) = ∑ n ∈ S, if (n : ZMod 5) = r then (1 : ℂ) else 0 := by
    rw [raySum, Finset.sum_boole]
  rw [hcard, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => rayIndicator_eq_charSum n r

end Characters5
end Brockian

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

