import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex Finset

namespace Chem

/-- `Fin 19` carries the commutative ring structure of `ZMod 19`
(the two types, and their additive group structures, are definitionally equal). -/
noncomputable local instance : CommRing (Fin 19) := (inferInstance : CommRing (ZMod 19))

/-- A primitive 19-th root of unity. -/

lemma ec_eq_exp (k : Fin 19) :
    ec k = Complex.exp (((2 * Real.pi * k.val / 19 : ℝ) : ℂ) * Complex.I) := by
  rw [ec, zeta19, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The Hückel eigenvalues. -/
