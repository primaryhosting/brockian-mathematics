/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as the module docstring below.)
import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Deutsch's algorithm decides whether `f : {0,1} → {0,1}` is constant or balanced using a
single query to the oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`.

The two-qubit state space is modelled as amplitude functions `Bool → Bool → ℂ`.  The
algorithm prepares `|0⟩|1⟩`, applies a Hadamard gate to each qubit, queries the oracle
exactly once, applies a Hadamard gate to the first qubit, and measures that qubit.
`QC.deutsch_correct` computes the resulting measurement distribution exactly.
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

/-- A two–qubit state: `ψ x y` is the amplitude of the computational basis state `|x, y⟩`. -/
abbrev State := Bool → Bool → ℂ

/-- The initial state `|0⟩ ⊗ |1⟩`. -/
noncomputable def init : State := fun x y => if x = false ∧ y = true then 1 else 0

/-- The Hadamard gate acting on the first qubit. -/
noncomputable def H₁ (ψ : State) : State :=
  fun x y => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ∑ z : Bool, (if x && z then -1 else 1) * ψ z y

/-- The Hadamard gate acting on the second qubit. -/
noncomputable def H₂ (ψ : State) : State :=
  fun x y => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ∑ z : Bool, (if y && z then -1 else 1) * ψ x z

/-- The oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`, expressed on amplitudes (`xor` is an
involution, so the amplitude of `|x, y⟩` in `U_f ψ` is the amplitude of `|x, y ⊕ f x⟩`
in `ψ`). -/
noncomputable def oracle (f : Bool → Bool) (ψ : State) : State :=
  fun x y => ψ x (xor y (f x))

/-- The final state of Deutsch's algorithm: prepare `|0⟩|1⟩`, apply a Hadamard gate to each
qubit, make **one** query to the oracle, and apply a Hadamard gate to the first qubit. -/
noncomputable def deutsch (f : Bool → Bool) : State :=
  H₁ (oracle f (H₁ (H₂ init)))

/-- The probability that measuring the first qubit of the final state yields `b`. -/
noncomputable def measProb (f : Bool → Bool) (b : Bool) : ℝ :=
  ∑ y : Bool, ‖deutsch f b y‖ ^ 2

/-- `f : {0,1} → {0,1}` is constant. -/
def Constant (f : Bool → Bool) : Prop := ∀ x y, f x = f y

/-- `f : {0,1} → {0,1}` is balanced, i.e. takes each value exactly once. -/
def Balanced (f : Bool → Bool) : Prop := f false ≠ f true

section Aux

private lemma sqrt2_inv_sq :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [← mul_inv, h]

/-- After the two Hadamard gates the state is the uniform superposition tensored with `|−⟩`. -/
private lemma pre_oracle (x y : Bool) :
    H₁ (H₂ init) x y = (2 : ℂ)⁻¹ * (if y then -1 else 1) := by
  simp only [H₁, H₂, init, Fintype.sum_bool]
  cases x <;> cases y <;> simp <;> linear_combination sqrt2_inv_sq

/-- The oracle query implements the phase kickback `|x⟩|−⟩ ↦ (-1)^(f x) |x⟩|−⟩`. -/
private lemma post_oracle (f : Bool → Bool) (x y : Bool) :
    oracle f (H₁ (H₂ init)) x y = (2 : ℂ)⁻¹ * (if xor y (f x) then -1 else 1) := by
  simp [oracle, pre_oracle]

/-- Closed form for the amplitudes of the final state. -/
private lemma deutsch_eq (f : Bool → Bool) (x y : Bool) :
    deutsch f x y =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (2 : ℂ)⁻¹ * (if y then -1 else 1) *
        ((if f false then -1 else 1) + (if x then -1 else 1) * (if f true then -1 else 1)) := by
  have h : deutsch f x y = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
      ∑ z : Bool, (if x && z then -1 else 1) * oracle f (H₁ (H₂ init)) z y := rfl
  rw [h, Fintype.sum_bool, post_oracle, post_oracle]
  cases x <;> cases y <;> cases hf0 : f false <;> cases hf1 : f true <;> simp <;> ring

end Aux

/-- **Deutsch's algorithm is correct.**  After a single query to the oracle `U_f`, measuring
the first qubit yields `0` with certainty when `f` is constant, and `1` with certainty when
`f` is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    measProb f false = (if f false = f true then 1 else 0) ∧
    measProb f true = (if f false = f true then 0 else 1) := by
  have hs : ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹‖ ^ 2 = (2 : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  constructor <;>
  · simp only [measProb, Fintype.sum_bool, deutsch_eq]
    cases hf0 : f false <;> cases hf1 : f true <;> norm_num [mul_pow, hs]

/-- Deutsch's algorithm *decides* constant-vs-balanced with a single oracle query: the
outcome `0` occurs with probability one exactly when `f` is constant, and with probability
zero exactly when `f` is balanced. -/
theorem deutsch_decides (f : Bool → Bool) :
    (measProb f false = 1 ↔ Constant f) ∧ (measProb f false = 0 ↔ Balanced f) := by
  have h := (deutsch_correct f).1
  constructor
  · rw [h]
    constructor
    · intro hx
      by_cases hc : f false = f true
      · intro x y; cases x <;> cases y <;> first | rfl | exact hc | exact hc.symm
      · simp [hc] at hx
    · intro hc
      simp [hc false true]
  · rw [h]
    constructor
    · intro hx
      by_cases hc : f false = f true
      · simp [hc] at hx
      · exact hc
    · intro hb
      simp [Balanced] at hb
      simp [hb]

end QC

