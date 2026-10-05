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

lemma ip_pauli_same (p q q' : Cfg) (u v : Bool) :
    ip (pauliOp p q (cw u)) (pauliOp p q' (cw v))
      = ((2 * Real.sqrt 2)⁻¹ : ℝ)^2 * (Dsum (xorCfg q q') u v : ℂ) := by
  have hterm : ∀ x : Cfg, star (pauliOp p q (cw u) x) * pauliOp p q' (cw v) x
      = ((2 * Real.sqrt 2)⁻¹ : ℝ)^2 *
        ((zsI (xorCfg q q') (xorCfg x p) * wI u (xorCfg x p) * wI v (xorCfg x p) : ℤ) : ℂ) := by
    intro x
    rw [← zsI_mul]
    simp only [pauliOp, cw, star_mul', Complex.star_def, Complex.conj_ofReal,
      map_intCast, Int.cast_mul]
    push_cast
    ring
  rw [ip, Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hterm x), ← Finset.mul_sum]
  congr 1
  rw [Dsum, Int.cast_sum]
  exact Equiv.sum_comp (Function.Involutive.toPerm _ (xorCfg_involutive p))
    (fun y => ((zsI (xorCfg q q') y * wI u y * wI v y : ℤ) : ℂ))

/-- If the `X`-parts differ, the codewords are moved to orthogonal sets of basis
states. -/
