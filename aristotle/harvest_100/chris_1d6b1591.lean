import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

namespace QC

/-- A two–qubit state is an amplitude vector indexed by `Bool × Bool`. -/
abbrev State := Bool × Bool → ℂ

/-- `1/√2`, the normalisation constant of the Hadamard gate. -/
noncomputable def isqrt2 : ℂ := (Real.sqrt 2)⁻¹

/-- The sign `(-1)^b`. -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- Hadamard gate acting on the first qubit. -/
noncomputable def H1 (v : State) : State :=
  fun p => isqrt2 * (v (false, p.2) + sgn p.1 * v (true, p.2))

/-- Hadamard gate acting on the second qubit. -/
noncomputable def H2 (v : State) : State :=
  fun p => isqrt2 * (v (p.1, false) + sgn p.2 * v (p.1, true))

/-- The (single) oracle query `U_f |x, y⟩ = |x, y ⊕ f x⟩`. -/
def oracle (f : Bool → Bool) (v : State) : State :=
  fun p => v (p.1, xor p.2 (f p.1))

/-- The input state `|0⟩ ⊗ |1⟩`. -/
def init : State := fun p => if p = (false, true) then 1 else 0

/-- The state produced by Deutsch's algorithm: `H₁ ∘ U_f ∘ H₂ ∘ H₁` applied to `|0,1⟩`,
using exactly one oracle query. -/
noncomputable def deutschState (f : Bool → Bool) : State :=
  H1 (oracle f (H2 (H1 init)))

/-- Probability that measuring the first qubit of the final state yields `0`. -/
noncomputable def probZero (f : Bool → Bool) : ℝ :=
  ‖deutschState f (false, false)‖ ^ 2 + ‖deutschState f (false, true)‖ ^ 2

lemma isqrt2_sq : isqrt2 * isqrt2 = 1 / 2 := by
  have h : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  rw [isqrt2, ← mul_inv, h2]
  norm_num

lemma norm_isqrt2_sq : ‖isqrt2‖ ^ 2 = 1 / 2 := by
  have h : ‖isqrt2‖ ^ 2 = ‖isqrt2 * isqrt2‖ := by
    rw [norm_mul]; ring
  rw [h, isqrt2_sq]
  norm_num

/-- Closed form of the two relevant amplitudes of the final state. -/
lemma deutschState_false (f : Bool → Bool) (y : Bool) :
    deutschState f (false, y) =
      isqrt2 * (1 / 2 * sgn y * (sgn (f false) + sgn (f true))) := by
  cases y <;>
    cases hf : f false <;> cases ht : f true <;>
      simp [deutschState, H1, H2, oracle, init, sgn, hf, ht] <;>
      ring_nf <;>
      (try
        first
          | (refine Or.inl ?_; linear_combination 2 * isqrt2_sq)
          | (refine Or.inl ?_; linear_combination -2 * isqrt2_sq)
          | linear_combination 2 * (isqrt2 : ℂ) * isqrt2_sq
          | linear_combination -2 * (isqrt2 : ℂ) * isqrt2_sq)

/-- `f` is constant. -/
def IsConstant (f : Bool → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: it takes the value `0` on exactly one input. -/
def IsBalanced (f : Bool → Bool) : Prop := ∀ x y, x ≠ y → f x ≠ f y

lemma isConstant_iff (f : Bool → Bool) : IsConstant f ↔ f false = f true := by
  constructor
  · intro h; exact h false true
  · intro h x y; cases x <;> cases y <;> simp [h, h.symm]

lemma isBalanced_iff (f : Bool → Bool) : IsBalanced f ↔ f false ≠ f true := by
  constructor
  · intro h; exact h false true (by simp)
  · intro h x y hxy
    cases x <;> cases y <;> simp_all [Ne.symm]

/-- **Deutsch's algorithm is correct.**  With a single query to the oracle for
`f : {0,1} → {0,1}`, measuring the first qubit yields `0` with probability `1`
exactly when `f` is constant, and with probability `0` exactly when `f` is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    (probZero f = 1 ↔ IsConstant f) ∧ (probZero f = 0 ↔ IsBalanced f) := by
  rw [isConstant_iff, isBalanced_iff]
  have h0 := deutschState_false f false
  have h1 := deutschState_false f true
  cases hf : f false <;> cases ht : f true <;>
    simp only [hf, ht, sgn, if_true] at h0 h1 <;>
    norm_num [probZero, h0, h1, norm_mul, mul_pow, norm_isqrt2_sq, hf, ht]

/-- Closed form of the remaining two amplitudes of the final state. -/
lemma deutschState_true (f : Bool → Bool) (y : Bool) :
    deutschState f (true, y) =
      isqrt2 * (1 / 2 * sgn y * (sgn (f false) - sgn (f true))) := by
  cases y <;>
    cases hf : f false <;> cases ht : f true <;>
      simp [deutschState, H1, H2, oracle, init, sgn, hf, ht] <;>
      ring_nf <;>
      (try
        first
          | (refine Or.inl ?_; linear_combination 2 * isqrt2_sq)
          | (refine Or.inl ?_; linear_combination -2 * isqrt2_sq)
          | linear_combination 2 * (isqrt2 : ℂ) * isqrt2_sq
          | linear_combination -2 * (isqrt2 : ℂ) * isqrt2_sq)

/-- The final state of the algorithm is a unit vector, so the quantities above really
are probabilities. -/
theorem deutschState_normalized (f : Bool → Bool) :
    ∑ p : Bool × Bool, ‖deutschState f p‖ ^ 2 = 1 := by
  have h0 := deutschState_false f false
  have h1 := deutschState_false f true
  have h2 := deutschState_true f false
  have h3 := deutschState_true f true
  cases hf : f false <;> cases ht : f true <;>
    simp only [hf, ht, sgn, if_true] at h0 h1 h2 h3 <;>
    norm_num [Fintype.sum_prod_type, h0, h1, h2, h3, norm_mul, mul_pow, norm_isqrt2_sq]

end QC

