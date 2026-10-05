/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

lemma vonNeumannEntropy_diagonal (d : n → ℝ) :
    vonNeumannEntropy (diagonal (fun i => (d i : ℂ))) = shannonEntropy d :=
  vonNeumannEntropy_eq_of_charpoly (isHermitian_diagonal_real d) d (Matrix.charpoly_diagonal _)

/-! ## The Holevo bound -/

/-- Holevo's bound for an ensemble of states that are diagonal in the computational basis,
measured by an arbitrary POVM. -/
