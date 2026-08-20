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

set_option grind.warning false

namespace QC

/-- A state of a two–qubit register: a complex amplitude for each computational
basis state `|x y⟩`, `x y : Bool`. -/
abbrev State := Bool × Bool → ℂ

/-- The sign `(-1)^b`. -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

@[simp] lemma sgn_false : sgn false = 1 := rfl

@[simp] lemma sgn_true : sgn true = -1 := rfl

/-- The Hadamard gate acting on the first qubit:
`|0⟩ ↦ (|0⟩+|1⟩)/√2`, `|1⟩ ↦ (|0⟩-|1⟩)/√2`. -/
noncomputable def hadamard₁ (ψ : State) : State :=
  fun p => (ψ (false, p.2) + sgn p.1 * ψ (true, p.2)) / (Real.sqrt 2 : ℝ)

/-- The Hadamard gate acting on the second qubit. -/
noncomputable def hadamard₂ (ψ : State) : State :=
  fun p => (ψ (p.1, false) + sgn p.2 * ψ (p.1, true)) / (Real.sqrt 2 : ℝ)

/-- The oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`.  It permutes the computational
basis, and since it is an involution, it acts on amplitudes by precomposition
with the same permutation. -/
def oracle (f : Bool → Bool) (ψ : State) : State :=
  fun p => ψ (p.1, xor p.2 (f p.1))

/-- The input state `|0⟩|1⟩`. -/
def initial : State := fun p => if p = (false, true) then 1 else 0

/-- The state produced by Deutsch's algorithm: prepare `|0⟩|1⟩`, apply `H ⊗ H`,
make a *single* query to the oracle, then apply `H` to the first qubit. -/
noncomputable def deutschState (f : Bool → Bool) : State :=
  hadamard₁ (oracle f (hadamard₂ (hadamard₁ initial)))

/-- The probability that measuring the first qubit of the final state yields `0`. -/
noncomputable def probZero (f : Bool → Bool) : ℝ :=
  ‖deutschState f (false, false)‖ ^ 2 + ‖deutschState f (false, true)‖ ^ 2

/-- The probability that measuring the first qubit of the final state yields `1`. -/
noncomputable def probOne (f : Bool → Bool) : ℝ :=
  ‖deutschState f (true, false)‖ ^ 2 + ‖deutschState f (true, true)‖ ^ 2

private lemma sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by simp

private lemma sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

@[simp] private lemma h1_initial_false (x : Bool) : hadamard₁ initial (x, false) = 0 := by
  cases x <;> simp [hadamard₁, initial]

@[simp] private lemma h1_initial_true (x : Bool) :
    hadamard₁ initial (x, true) = 1 / (Real.sqrt 2 : ℝ) := by
  cases x <;> simp [hadamard₁, initial]

/-- After `H ⊗ H` the register is in the state `(|0⟩+|1⟩)(|0⟩-|1⟩)/2`. -/
private lemma h2_h1_initial (p : Bool × Bool) :
    hadamard₂ (hadamard₁ initial) p = sgn p.2 / 2 := by
  obtain ⟨x, y⟩ := p
  have hne := sqrt2_ne
  cases y <;> simp only [hadamard₂, h1_initial_false, h1_initial_true, sgn_false, sgn_true] <;>
    field_simp <;> rw [sqrt2_sq] <;> ring

/-- The single oracle query produces the phase kickback `(-1)^{f x}`. -/
private lemma oracle_state (f : Bool → Bool) (p : Bool × Bool) :
    oracle f (hadamard₂ (hadamard₁ initial)) p = sgn (f p.1) * sgn p.2 / 2 := by
  obtain ⟨x, y⟩ := p
  simp only [oracle, h2_h1_initial]
  cases y <;> cases hfx : f x <;> simp

/-- The amplitudes of the final state on the basis states with first qubit `0`. -/
lemma deutschState_false (f : Bool → Bool) (y : Bool) :
    deutschState f (false, y) =
      (sgn (f false) + sgn (f true)) * sgn y / (2 * (Real.sqrt 2 : ℝ)) := by
  have hne := sqrt2_ne
  simp only [deutschState, hadamard₁, oracle_state, sgn_false]
  field_simp

/-- The amplitudes of the final state on the basis states with first qubit `1`. -/
lemma deutschState_true (f : Bool → Bool) (y : Bool) :
    deutschState f (true, y) =
      (sgn (f false) - sgn (f true)) * sgn y / (2 * (Real.sqrt 2 : ℝ)) := by
  have hne := sqrt2_ne
  simp only [deutschState, hadamard₁, oracle_state, sgn_true]
  field_simp
  ring

/-- **Deutsch's algorithm is correct**: after a *single* query to the oracle for
`f : {0,1} → {0,1}`, measuring the first qubit yields `0` with probability `1`
when `f` is constant (`f false = f true`), and with probability `0` when `f` is
balanced (`f false ≠ f true`). -/
theorem deutsch_correct (f : Bool → Bool) :
    probZero f = if f false = f true then 1 else 0 := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [probZero, deutschState_false]
  cases hf0 : f false <;> cases hf1 : f true <;>
    simp [div_pow, abs_of_pos hs, mul_pow, hs2] <;> norm_num

/-- Measuring the first qubit gives `0` with certainty exactly when `f` is constant. -/
theorem deutsch_constant_iff (f : Bool → Bool) :
    probZero f = 1 ↔ f false = f true := by
  rw [deutsch_correct]
  cases hf0 : f false <;> cases hf1 : f true <;> simp

/-- Measuring the first qubit never gives `0` exactly when `f` is balanced. -/
theorem deutsch_balanced_iff (f : Bool → Bool) :
    probZero f = 0 ↔ f false ≠ f true := by
  rw [deutsch_correct]
  cases hf0 : f false <;> cases hf1 : f true <;> simp

/-- Sanity check: the final state is a unit vector, i.e. the two measurement
outcomes for the first qubit have probabilities summing to `1`. -/
theorem probZero_add_probOne (f : Bool → Bool) : probZero f + probOne f = 1 := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [probZero, probOne, deutschState_false, deutschState_true]
  cases hf0 : f false <;> cases hf1 : f true <;>
    simp [div_pow, abs_of_pos hs, mul_pow, hs2] <;> norm_num

end QC

