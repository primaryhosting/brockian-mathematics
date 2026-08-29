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

lemma isPrimitiveRoot_zeta11 : IsPrimitiveRoot zeta11 11 := by
  simpa [zeta11] using Complex.isPrimitiveRoot_exp 11 (by norm_num)

