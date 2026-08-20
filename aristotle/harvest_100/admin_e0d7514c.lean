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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` given by `x ↦ ω ^ x`. -/
noncomputable def e (x : ZMod 5) : ℂ := ω ^ x.val

/-- The number of elements of `S` lying on the ray `r` modulo `5`. -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ :=
  (Finset.filter (fun n : ℕ => (n : ZMod 5) = r) S).card

/-- Expanding a sum over `ZMod 5` into its five summands. -/
theorem sum_zmod_five (g : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, g a = g 0 + g 1 + g 2 + g 3 + g 4 := by
  show ∑ a : Fin 5, g a = _
  rw [Fin.sum_univ_five]

/-- The fifth roots of unity sum to zero. -/
theorem geom_sum_omega : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h := (Complex.isPrimitiveRoot_exp 5 (by norm_num)).geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ, ω] at h ⊢
  linear_combination h

/-- Orthogonality of the characters of `ZMod 5`. -/
theorem sum_char_eq (t : ZMod 5) : ∑ a : ZMod 5, e (a * t) = if t = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases h : t = 0
  · subst h; simp [e]
  · rw [if_neg h,
      Fintype.sum_equiv (Equiv.mulRight₀ t h) (fun a => e (a * t)) e (fun _ => rfl),
      sum_zmod_five]
    show (1 : ℂ) + ω ^ 1 + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0
    linear_combination geom_sum_omega

/-- The indicator of the ray `r` as a character sum. -/
theorem rayIndicator_eq_charSum (n : ℕ) (r : ZMod 5) :
    (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  rw [sum_char_eq]
  simp only [sub_eq_zero]
  split <;> norm_num

/-- Ray-count identity: the number of elements of `S` on the ray `r` modulo `5` equals
`(1/5) ∑_{a : ZMod 5} ∑_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ) = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  rw [Finset.sum_comm, Finset.mul_sum, raySum,
    Finset.card_filter (fun n : ℕ => (n : ZMod 5) = r) S]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_congr rfl fun n _ => rayIndicator_eq_charSum n r

end Characters5
end Brockian

