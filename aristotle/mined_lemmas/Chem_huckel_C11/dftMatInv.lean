/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

noncomputable def dftMatInv : Matrix (Fin 11) (Fin 11) ℂ :=
  Matrix.of fun j k => (11 : ℂ)⁻¹ * echar (-(j * k))

