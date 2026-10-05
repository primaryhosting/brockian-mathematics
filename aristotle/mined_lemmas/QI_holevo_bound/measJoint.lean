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

noncomputable def measJoint [Fintype X] [Fintype Y] (p : X → ℝ) (ρ : X → Matrix n n ℂ)
    (E : Y → Matrix n n ℂ) : X → Y → ℝ :=
  fun x y => p x * (Matrix.trace (ρ x * E y)).re

/-- The accessible information of the ensemble `{p x, ρ x}` with respect to measurements with
outcomes in `Y`: the supremum of the mutual information over all POVMs. -/
