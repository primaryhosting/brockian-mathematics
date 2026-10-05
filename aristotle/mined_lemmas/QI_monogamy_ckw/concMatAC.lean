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

noncomputable def concMatAC (psi : Fin 2 → Fin 2 → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun j l =>
    -(psi 0 j 0 * psi 1 l 1) + psi 0 j 1 * psi 1 l 0 + psi 1 j 0 * psi 0 l 1
      - psi 1 j 1 * psi 0 l 0

/-- The squared Wootters concurrence attached to a `2 × 2` concurrence matrix `T`:
if `d₁ ≥ d₂ ≥ 0` are the singular values of `T`, then the concurrence of the
corresponding (rank ≤ 2) two-qubit mixed state is `C = d₁ - d₂`, so
`C² = d₁² + d₂² - 2 d₁ d₂ = ‖T‖_F² - 2 |det T|`. -/
