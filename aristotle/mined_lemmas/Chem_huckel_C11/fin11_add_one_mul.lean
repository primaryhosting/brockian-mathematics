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

lemma fin11_add_one_mul (i k : Fin 11) : (i + 1) * k = i * k + k := by revert i k; decide

/-- The diagonal matrix of eigenvalues. -/
