import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any comment, so the header block above sits
directly after the single `import Mathlib` line.)
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

open Matrix Complex

/-- Amplitudes of a pure state of three qubits `A`, `B`, `C`:
`ψ i j k` is the coefficient of the computational basis vector `|i j k⟩`. -/
abbrev Amp : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The reduced density matrix of qubit `A`, i.e. `Tr_{BC} |ψ⟩⟨ψ|`. -/

noncomputable def concurrenceSq (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  ((ρ * spinFlip ρ).trace).re -
    2 * Real.sqrt
      ((((ρ * spinFlip ρ).trace ^ 2 - ((ρ * spinFlip ρ) * (ρ * spinFlip ρ)).trace) / 2).re)

/-- Justification of the definition of `concurrenceSq`: if the matrix `M = ρ ρ̃` has spectrum
`{l₁, l₂, 0, 0}` with `0 ≤ l₂ ≤ l₁` (so that `tr M = l₁ + l₂` and `e₂ M = l₁ l₂`), then
`concurrenceSq ρ` is exactly Wootters' `(√l₁ - √l₂ - √0 - √0)²`. -/
