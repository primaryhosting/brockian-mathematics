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

noncomputable def holevoChi [Fintype X] (p : X → ℝ) (ρ : X → Matrix n n ℂ) : ℝ :=
  vonNeumannEntropy (∑ x, (p x : ℂ) • ρ x) - ∑ x, p x * vonNeumannEntropy (ρ x)

/-- The joint distribution of the label `x` and the measurement outcome `y` obtained by
measuring the ensemble `{p x, ρ x}` with the POVM `E`. -/
