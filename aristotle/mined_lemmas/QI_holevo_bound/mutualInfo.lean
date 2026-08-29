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

noncomputable def mutualInfo [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, r x y * Real.log (r x y / ((∑ y', r x y') * (∑ x', r x' y)))

/-- The log-sum inequality. -/
