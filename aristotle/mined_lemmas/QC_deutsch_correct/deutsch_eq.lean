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
