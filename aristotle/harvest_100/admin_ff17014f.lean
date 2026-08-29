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

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` valued in `ℂ`. -/
noncomputable def e (a : ZMod 5) : ℂ := ω ^ a.val

theorem isPrimitiveRoot_ω : IsPrimitiveRoot ω 5 := by
  simpa [ω] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem sum_e : ∑ a : ZMod 5, e a = 0 := by
  have h := isPrimitiveRoot_ω.geom_sum_eq_zero (by norm_num)
  rw [← h]
  exact Fin.sum_univ_eq_sum_range (fun i => ω ^ i) 5

/-- Orthogonality: the character sum over `ZMod 5` detects `x = 0`. -/
theorem sum_e_mul (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then (5 : ℂ) else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · simp [hx, e]
  · rw [if_neg hx]
    rw [← sum_e]
    exact Fintype.sum_equiv (Equiv.mulRight₀ x hx) _ _ (fun a => rfl)

/-- The indicator of the ray `{n : n ≡ r}` as a character sum. -/
theorem rayIndicator_eq_charSum (n : ℕ) (r : ZMod 5) :
    (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  rw [sum_e_mul]
  by_cases h : (n : ZMod 5) = r
  · simp [h]
  · rw [if_neg h, if_neg (by simpa [sub_eq_zero] using h)]
    ring

/-- The number of elements of `S` lying on the ray `r` modulo `5`.

The binder type `n : ℕ` is stated explicitly: writing `fun n => (n : ZMod 5) = r` makes Lean read
`(n : ZMod 5)` as a type ascription, giving the binder type `ZMod 5` and silently coercing `S` to
`Finset (ZMod 5)` (i.e. taking its image), which would count residues rather than elements of `S`. -/
noncomputable def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ :=
  (S.filter fun n : ℕ => (n : ZMod 5) = r).card

theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ) = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  have hcard : raySum S r = ∑ n ∈ S, if (n : ZMod 5) = r then 1 else 0 :=
    Finset.card_filter (fun n : ℕ => (n : ZMod 5) = r) S
  rw [hcard, Nat.cast_sum, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rayIndicator_eq_charSum n r]
  split <;> simp

end Characters5
end Brockian

