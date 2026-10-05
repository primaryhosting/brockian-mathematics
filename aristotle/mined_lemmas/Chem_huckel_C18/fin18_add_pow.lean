/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma fin18_add_pow {u : ℂ} (hu : u ^ 18 = 1) (a b : Fin 18) :
    u ^ ((a + b : Fin 18) : ℕ) = u ^ (a : ℕ) * u ^ (b : ℕ) := by
  rw [Fin.val_add, pow_mod18 hu, pow_add]

