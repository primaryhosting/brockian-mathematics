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

theorem trace_spinFlip_add_trace_spinFlip (ψ : Amp) :
    (rhoAB ψ * spinFlip (rhoAB ψ)).trace + (rhoAC ψ * spinFlip (rhoAC ψ)).trace
      = 4 * (rhoA ψ).det := by
  simp [rhoAB, rhoAC, rhoA, spinFlip, YY, sigmaY, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.det_fin_two, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring_nf

