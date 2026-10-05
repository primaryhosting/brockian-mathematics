/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above
-- is written as a plain block comment; it is repeated as a module docstring below.)

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
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

/-! ## Setup

The nine qubits of the Shor code are indexed by `Idx = Fin 3 × Fin 3`: the first
component is the block (of the outer phase-flip code), the second the position
inside the block (the inner bit-flip repetition code).

A computational basis state is a configuration `Cfg = Idx → Bool`, and a state
vector is a function `St = Cfg → ℂ` giving the amplitude of each basis state.
-/

/-- Index set of the nine qubits: `(block, position)`. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- A computational basis label for the nine qubits. -/
abbrev Cfg : Type := Idx → Bool

/-- A state vector of the nine-qubit register. -/
abbrev St : Type := Cfg → ℂ

/-- The standard hermitian inner product on the nine-qubit state space,
antilinear in the first argument. -/

lemma ip_pauli_diff {p p' : Cfg} (q q' : Cfg) {i j : Idx}
    (hi : ∀ k, p k = true → k = i) (hj : ∀ k, p' k = true → k = j)
    (hne : p ≠ p') (u v : Bool) :
    ip (pauliOp p q (cw u)) (pauliOp p' q' (cw v)) = 0 := by
  rw [ip]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hu : wI u (xorCfg x p) = 0
  · simp [pauliOp, cw, hu]
  by_cases hv : wI v (xorCfg x p') = 0
  · simp [pauliOp, cw, hv]
  exfalso
  have hbc : BC (xorCfg (xorCfg x p) (xorCfg x p')) :=
    BC_xor (wI_ne_zero_BC hu) (wI_ne_zero_BC hv)
  have hd : xorCfg (xorCfg x p) (xorCfg x p') = xorCfg p p' := by
    funext k
    simp only [xorCfg]
    cases x k <;> cases p k <;> cases p' k <;> rfl
  rw [hd] at hbc
  have hsupp : ∀ k, xorCfg p p' k = true → k = i ∨ k = j := by
    intro k hk
    by_cases h1 : p k = true
    · exact Or.inl (hi k h1)
    · have : p' k = true := by
        simp only [xorCfg] at hk
        cases hp : p k <;> cases hp' : p' k <;> simp_all
      exact Or.inr (hj k this)
  have := BC_supp_eq_zero hbc hsupp
  refine hne (funext fun k => ?_)
  have hk := congrFun this k
  simp only [xorCfg] at hk
  cases hp : p k <;> cases hp' : p' k <;> simp_all

/-! ## Knill–Laflamme conditions for single-qubit Paulis -/

