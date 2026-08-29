/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain block comment; it is repeated as a module
-- docstring immediately after the imports.)

import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

namespace QI

/-- The `±1` phase attached to a boolean value: `sgn b = (-1)^b`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- `f` is constant. -/
def IsConstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: exactly half of the `2 ^ n` inputs are mapped to `true`. -/
def IsBalanced {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  2 * (Finset.univ.filter fun x : Fin n → Bool => f x = true).card = 2 ^ n

/-- The amplitude of the basis state `|y⟩` in the state
`H^{⊗n} U_f H^{⊗n} |0…0⟩` produced by the Deutsch–Jozsa circuit using a *single*
query to the phase oracle `U_f : |x⟩ ↦ (-1)^{f x} |x⟩`, namely
`2 ^ (-n) * ∑ x, (-1) ^ (f x + x ⬝ y)`. -/
noncomputable def djState {n : ℕ} (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) : ℝ :=
  (∑ x : Fin n → Bool, sgn (f x) * ∏ i, (if x i && y i then (-1 : ℝ) else 1)) / 2 ^ n

/-- The amplitude of the all-zeros outcome: this is the quantity whose square is the
probability that the Deutsch–Jozsa algorithm measures `0…0`. -/
noncomputable def djAmp {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  djState f (fun _ => false)

lemma djAmp_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    djAmp f = (∑ x : Fin n → Bool, sgn (f x)) / 2 ^ n := by
  simp [djAmp, djState]

/-- The Deutsch–Jozsa sum equals `2 ^ n - 2 * #{x | f x = true}`. -/
lemma sum_sgn {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (∑ x : Fin n → Bool, sgn (f x))
      = (2 : ℝ) ^ n - 2 * ((Finset.univ.filter fun x : Fin n → Bool => f x = true).card : ℝ) := by
  classical
  have h : ∀ x : Fin n → Bool, sgn (f x) = 1 - 2 * (if f x = true then (1 : ℝ) else 0) := by
    intro x; by_cases hx : f x = true <;> simp [sgn, hx]
    norm_num
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp

/-- A constant function produces the all-zeros outcome with certainty:
the amplitude is `±1`. -/
lemma abs_djAmp_of_isConstant {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsConstant f) :
    |djAmp f| = 1 := by
  classical
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rcases Bool.eq_false_or_eq_true (f (fun _ => false)) with hc | hc
  · have hfilter : (Finset.univ.filter fun x : Fin n → Bool => f x = true) = Finset.univ := by
      apply Finset.filter_eq_self.2
      intro x _
      simp [hf x (fun _ => false), hc]
    have hcard : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by
      simp
    rw [djAmp_eq, sum_sgn, hfilter, hcard]
    rw [show (2 : ℝ) ^ n - 2 * 2 ^ n = -(2 ^ n) by ring]
    rw [neg_div, div_self (ne_of_gt hpos), abs_neg, abs_one]
  · have hfilter : (Finset.univ.filter fun x : Fin n → Bool => f x = true) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro x _
      simp [hf x (fun _ => false), hc]
    rw [djAmp_eq, sum_sgn, hfilter]
    simp

/-- A balanced function produces the all-zeros outcome with probability zero:
the amplitude vanishes. -/
lemma djAmp_of_isBalanced {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBalanced f) :
    djAmp f = 0 := by
  classical
  have hr : 2 * ((Finset.univ.filter fun x : Fin n → Bool => f x = true).card : ℝ)
      = (2 : ℝ) ^ n := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hf
    push_cast at this
    simpa using this
  rw [djAmp_eq, sum_sgn, hr]
  simp

/--
**Deutsch–Jozsa.**  Given the promise that `f : (Fin n → Bool) → Bool` is either constant
or balanced, the single-query Deutsch–Jozsa circuit decides which: the all-zeros outcome
of `H^{⊗n} U_f H^{⊗n} |0…0⟩` has amplitude of modulus `1` exactly when `f` is constant,
and amplitude `0` exactly when `f` is balanced.  Hence one query to the oracle suffices.
-/
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hpromise : IsConstant f ∨ IsBalanced f) :
    (IsConstant f ↔ |djAmp f| = 1) ∧ (IsBalanced f ↔ djAmp f = 0) := by
  constructor
  · constructor
    · exact abs_djAmp_of_isConstant
    · intro h
      rcases hpromise with hc | hb
      · exact hc
      · rw [djAmp_of_isBalanced hb] at h
        simp at h
  · constructor
    · exact djAmp_of_isBalanced
    · intro h
      rcases hpromise with hc | hb
      · have := abs_djAmp_of_isConstant hc
        rw [h] at this
        simp at this
      · exact hb

/-- Sanity check: the promise is satisfiable on the balanced side. -/
example : IsBalanced (fun x : Fin 1 → Bool => x 0) := by
  decide

/-- Sanity check: the promise is satisfiable on the constant side. -/
example : IsConstant (fun _ : Fin 1 → Bool => true) := by
  decide

end QI

#print axioms QI.deutsch_jozsa

