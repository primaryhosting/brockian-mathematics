import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

/-- The Hermitian form attached to a matrix `A`: `x ↦ Re (star x ⬝ᵥ (A *ᵥ x))`. -/

noncomputable def hermForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ x)).re

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity).  For a non-Hermitian matrix the value is `0`. -/
