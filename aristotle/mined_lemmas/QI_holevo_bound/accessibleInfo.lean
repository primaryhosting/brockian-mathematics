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

noncomputable def accessibleInfo [Fintype X] (p : X → ℝ) (ρ : X → Matrix n n ℂ)
    (Y : Type) [Fintype Y] : ℝ :=
  sSup {t | ∃ E : Y → Matrix n n ℂ, IsPOVM E ∧ t = mutualInfo (measJoint p ρ E)}

/-- A family of matrices that is simultaneously diagonalizable by a unitary; for Hermitian
matrices this is equivalent to the family being commuting. -/
