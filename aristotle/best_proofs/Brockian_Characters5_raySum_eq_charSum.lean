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

/-- The standard additive character `e` of `ZMod 5`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := ω ^ x.val

/-- The number of elements of `S` lying on the ray `r`, i.e. congruent to `r` modulo `5`.
(The binder `n : ℕ` is written explicitly so that the filter really ranges over the natural
numbers of `S`, rather than over the image of `S` in `ZMod 5`.) -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ := (S.filter fun n : ℕ => (n : ZMod 5) = r).card

lemma omega_isPrimitiveRoot : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [ω] using h

/-- The full character sum over `ZMod 5` vanishes: `1 + ω + ω² + ω³ + ω⁴ = 0`. -/
lemma sum_e_univ : ∑ b : ZMod 5, e b = 0 := by
  have h : ∑ b : ZMod 5, e b = ∑ i ∈ Finset.range 5, ω ^ i := rfl
  rw [h]
  exact omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)

/-- Orthogonality of the characters of `ZMod 5`. -/
lemma sum_e_mul (t : ZMod 5) :
    ∑ a : ZMod 5, e (a * t) = if t = 0 then (5 : ℂ) else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases ht : t = 0
  · subst ht
    simp [e]
  · rw [if_neg ht]
    have h : ∑ a : ZMod 5, e (a * t) = ∑ b : ZMod 5, e b :=
      Fintype.sum_equiv (Equiv.mulRight₀ t ht) _ _ fun _ => rfl
    rw [h, sum_e_univ]

/-- The indicator of the ray `r` written as a character sum. -/
lemma rayIndicator_eq_charSum (x r : ZMod 5) :
    (if x = r then (1 : ℂ) else 0) = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * (x - r)) := by
  rw [sum_e_mul]
  by_cases h : x = r <;> simp [h, sub_eq_zero]

/-- Ray-count identity: the number of elements of `S` on the ray `r` equals
`(1/5) Σ_{a : ZMod 5} Σ_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ) = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  have hcard : raySum S r = ∑ n ∈ S, if (n : ZMod 5) = r then 1 else 0 :=
    Finset.card_filter (fun n : ℕ => (n : ZMod 5) = r) S
  have h1 : ((raySum S r : ℕ) : ℂ) = ∑ n ∈ S, if (n : ZMod 5) = r then (1 : ℂ) else 0 := by
    rw [hcard, Nat.cast_sum (R := ℂ) S fun n => if (n : ZMod 5) = r then 1 else 0]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : (n : ZMod 5) = r <;> simp [hn]
  rw [h1, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => rayIndicator_eq_charSum _ _

end Characters5
end Brockian

