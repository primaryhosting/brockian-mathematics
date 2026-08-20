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

noncomputable def rhoAC (ψ : Amp) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => ∑ j, ψ p.1 j p.2 * (starRingEnd ℂ) (ψ q.1 j q.2)

/-- The Pauli matrix `σ_y`. -/
