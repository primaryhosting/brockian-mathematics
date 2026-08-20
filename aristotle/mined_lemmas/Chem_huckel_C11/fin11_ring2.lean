import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma fin11_ring2 (j k : Fin 11) : (j - 1) * k = j * k + -k := by
  have h : ∀ a b : ZMod 11, (a - 1) * b = a * b + -b := by
    intro a b; ring
  exact h j k

