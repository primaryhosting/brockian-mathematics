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

def IsPOVM [Fintype Y] (E : Y → Matrix n n ℂ) : Prop :=
  (∀ y, (E y).PosSemidef) ∧ ∑ y, E y = 1

open Classical in
/-- The von Neumann entropy of a Hermitian matrix (defined as `0` on non-Hermitian input). -/
