import Mathlib

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

/-
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: passed (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Matrix

/-- **Spectral theorem (finite dimensions).**
Every Hermitian matrix `A` over an `RCLike` field (e.g. `ℂ`) is unitarily diagonalizable with
real eigenvalues: there exist a unitary matrix `U` and a real-valued function `d` such that
`A = U * diagonal (d) * Uᴴ`, and moreover `Uᴴ * A * U = diagonal d`.

This is essentially `Matrix.IsHermitian.spectral_theorem` from Mathlib, restated in the
elementary `U * D * Uᴴ` form. -/
theorem spectral_theorem_finite {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ (U : Matrix n n 𝕜) (d : n → ℝ),
      U ∈ Matrix.unitaryGroup n 𝕜 ∧
      A = U * diagonal (fun i => (d i : 𝕜)) * Uᴴ ∧
      Uᴴ * A * U = diagonal (fun i => (d i : 𝕜)) := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n 𝕜), hA.eigenvalues,
    (hA.eigenvectorUnitary).2, ?_, ?_⟩
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.conjTranspose, Function.comp_def] using h
  · have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [Matrix.conjTranspose, Function.comp_def, mul_assoc] using h

end QPhys

