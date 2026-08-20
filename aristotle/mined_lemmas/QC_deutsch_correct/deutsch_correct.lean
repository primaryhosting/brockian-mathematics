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
