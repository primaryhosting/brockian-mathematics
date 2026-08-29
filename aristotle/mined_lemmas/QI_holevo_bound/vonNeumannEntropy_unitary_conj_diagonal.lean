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

lemma vonNeumannEntropy_unitary_conj_diagonal {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (d : n → ℝ) :
    vonNeumannEntropy (U * diagonal (fun i => (d i : ℂ)) * star U) = shannonEntropy d :=
  vonNeumannEntropy_eq_of_charpoly (isHermitian_unitary_conj_diagonal U d) d
    (by rw [charpoly_unitary_conj hU, Matrix.charpoly_diagonal])

/-- Holevo's bound for a fixed POVM `E`: the mutual information between the label and the
measurement outcome is at most the Holevo χ quantity of the ensemble. -/
