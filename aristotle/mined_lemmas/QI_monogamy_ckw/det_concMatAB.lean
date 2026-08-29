/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment and is reproduced verbatim as the module docstring below.)

import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
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

open ComplexConjugate

/-! ## Setup

A pure state of three qubits `A`, `B`, `C` is given by its amplitudes
`psi i j k` in the computational basis `|ijk⟩`, `i j k : Fin 2`.
All quantities below are homogeneous of degree `(2,2)` in `(psi, conj psi)`, so
they are the usual physical quantities as soon as `psi` is normalized; no
normalization hypothesis is needed for the statements.
-/

/-- The reduced density matrix of qubit `A`,
`(ρ_A)_{i i'} = ∑_{j k} ψ_{ijk} conj ψ_{i'jk}`. -/

theorem det_concMatAB (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) :
    (concMatAB psi).det = -hyperdet psi := by
  simp only [concMatAB, hyperdet, Matrix.det_fin_two, Matrix.of_apply]
  ring

/-- The determinant of the `AC` concurrence matrix is (minus) the hyperdeterminant. -/
