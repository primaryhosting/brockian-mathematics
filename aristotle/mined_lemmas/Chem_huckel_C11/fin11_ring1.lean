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

lemma fin11_ring1 (j k l : Fin 11) : j * l + -(l * k) = l * (j - k) := by
  have h : ∀ a b c : ZMod 11, a * c + -(c * b) = c * (a - b) := by
    intro a b c; ring
  exact h j k l

