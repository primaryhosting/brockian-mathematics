import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-! ## The three-qubit Hilbert space -/

/-- Computational basis index for three qubits. -/
abbrev Q : Type := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` matrix. -/

theorem no_lhv (v : LHV) : ¬ v.MerminConstraints := by
  rintro ⟨h1, h2, h3, h4⟩
  have key : (v.x 0 * v.x 1 * v.x 2) * ((v.y 0) ^ 2 * (v.y 1) ^ 2 * (v.y 2) ^ 2) = -1 := by
    have : (v.x 0 * v.y 1 * v.y 2) * ((v.y 0 * v.x 1 * v.y 2) * (v.y 0 * v.y 1 * v.x 2)) =
        (-1 : ℝ) * ((-1) * (-1)) := by rw [h1, h2, h3]
    nlinarith [this]
  have hy0 : (v.y 0) ^ 2 = 1 := by rcases v.hy 0 with h | h <;> rw [h] <;> norm_num
  have hy1 : (v.y 1) ^ 2 = 1 := by rcases v.hy 1 with h | h <;> rw [h] <;> norm_num
  have hy2 : (v.y 2) ^ 2 = 1 := by rcases v.hy 2 with h | h <;> rw [h] <;> norm_num
  rw [hy0, hy1, hy2, h4] at key
  norm_num at key

/-! ## The Mermin–GHZ paradox -/

/-- **GHZ nonlocality (Mermin's paradox).**

The three-qubit GHZ state `|000⟩ + |111⟩` is a simultaneous eigenvector of the four
commuting observables `X⊗Y⊗Y`, `Y⊗X⊗Y`, `Y⊗Y⊗X` (eigenvalue `-1`) and `X⊗X⊗X`
(eigenvalue `+1`); these are deterministic predictions of quantum mechanics.  Yet no
deterministic local hidden-variable assignment of `±1` outcomes to the local `X` and `Y`
measurements can reproduce all four of them. -/
