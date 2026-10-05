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

def SimultaneouslyDiagonalizable [Fintype X] (ρ : X → Matrix n n ℂ) : Prop :=
  ∃ U : Matrix n n ℂ, U ∈ Matrix.unitaryGroup n ℂ ∧
    ∀ x, ∃ d : n → ℝ, ρ x = U * diagonal (fun i => (d i : ℂ)) * star U

/-- If the characteristic polynomial of a Hermitian matrix splits with real roots `d`, its
von Neumann entropy is the Shannon entropy of `d`. -/
