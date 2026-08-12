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

/-! ## The two-qubit state space

A state of two qubits is a function `Bool × Bool → ℂ` assigning an amplitude to each
computational basis state `|x y⟩`. -/

/-- The sign `(-1)^b`. -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- `√2`, as a complex number. -/
noncomputable def rt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

lemma rt2_ne_zero : rt2 ≠ 0 := by
  simp only [rt2, ne_eq, Complex.ofReal_eq_zero]
  positivity

/-- Hadamard applied to the first qubit. -/
noncomputable def H1 (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => (psi (false, p.2) + sgn p.1 * psi (true, p.2)) / rt2

/-- Hadamard applied to the second qubit. -/
noncomputable def H2 (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => (psi (p.1, false) + sgn p.2 * psi (p.1, true)) / rt2

/-- The oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩` for `f : Bool → Bool`. -/
def oracle (f : Bool → Bool) (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => psi (p.1, xor p.2 (f p.1))

/-- The initial state `|0⟩|1⟩`. -/
def init : Bool × Bool → ℂ := fun p => if p = (false, true) then 1 else 0

/-- The state produced by Deutsch's algorithm: prepare `|0⟩|1⟩`, apply a Hadamard to each
qubit, make a *single* query to the oracle, then apply a Hadamard to the first qubit. -/
noncomputable def deutschState (f : Bool → Bool) : Bool × Bool → ℂ :=
  H1 (oracle f (H2 (H1 init)))

/-- The probability that measuring the first qubit of the final state yields `0`. -/
noncomputable def prob0 (f : Bool → Bool) : ℝ :=
  ‖deutschState f (false, false)‖ ^ 2 + ‖deutschState f (false, true)‖ ^ 2

theorem rt2_sq : rt2 ^ 2 = 2 := by
  simp only [rt2, ← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- Explicit form of the amplitudes of the final state on the first qubit being `0`. -/
lemma deutschState_false (f : Bool → Bool) (y : Bool) :
    deutschState f (false, y) = sgn y * (sgn (f false) + sgn (f true)) / (2 * rt2) := by
  simp only [deutschState, H1, H2, oracle, init, sgn]
  cases y <;> cases f false <;> cases f true <;> simp <;>
    first
      | (refine Or.inl ?_; ring)
      | (field_simp [rt2_ne_zero]; simp only [rt2_sq])

/-- **Deutsch's algorithm is correct.**  After a single query to the oracle `U_f`, measuring
the first qubit yields outcome `0` with probability `1` exactly when `f` is constant, and with
probability `0` exactly when `f` is balanced. -/
theorem deutsch_correct (f : Bool → Bool) :
    prob0 f = if f false = f true then 1 else 0 := by
  have hnorm : ‖rt2‖ = Real.sqrt 2 := by
    simp [rt2, Real.sqrt_nonneg]
  simp only [prob0, deutschState_false, sgn]
  cases f false <;> cases f true <;>
    simp [hnorm, div_pow] <;>
    · field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num

/-- The probability that measuring the first qubit of the final state yields `1`. -/
noncomputable def prob1 (f : Bool → Bool) : ℝ :=
  ‖deutschState f (true, false)‖ ^ 2 + ‖deutschState f (true, true)‖ ^ 2

/-- Explicit form of the amplitudes of the final state on the first qubit being `1`. -/
lemma deutschState_true (f : Bool → Bool) (y : Bool) :
    deutschState f (true, y) = sgn y * (sgn (f false) - sgn (f true)) / (2 * rt2) := by
  simp only [deutschState, H1, H2, oracle, init, sgn]
  cases y <;> cases f false <;> cases f true <;> simp <;>
    field_simp [rt2_ne_zero] <;> (simp only [rt2_sq]; try ring)

/-- The complementary outcome: the first qubit is measured to be `1` exactly when `f` is
balanced. -/
theorem deutsch_prob1 (f : Bool → Bool) :
    prob1 f = if f false = f true then 0 else 1 := by
  have hnorm : ‖rt2‖ = Real.sqrt 2 := by
    simp [rt2, Real.sqrt_nonneg]
  simp only [prob1, deutschState_true, sgn]
  cases f false <;> cases f true <;>
    simp [hnorm, div_pow] <;>
    · field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num

/-- Sanity check: the final state is normalized, i.e. the two measurement outcomes for the
first qubit have probabilities summing to `1`. -/
theorem deutsch_prob_total (f : Bool → Bool) : prob0 f + prob1 f = 1 := by
  rw [deutsch_correct, deutsch_prob1]
  by_cases h : f false = f true <;> simp [h]

/-- Restatement: the algorithm decides constant vs. balanced. -/
theorem deutsch_decides (f : Bool → Bool) :
    (prob0 f = 1 ↔ f false = f true) ∧ (prob0 f = 0 ↔ f false ≠ f true) := by
  rw [deutsch_correct]
  by_cases h : f false = f true <;> simp [h]

end QC

#print axioms QC.deutsch_correct
#print axioms QC.deutsch_decides
#print axioms QC.deutsch_prob1
#print axioms QC.deutsch_prob_total

