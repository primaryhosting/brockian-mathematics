/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma exp_add_inv (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹
      = 2 * Complex.cos (θ : ℂ) := by
  rw [← Complex.exp_neg, Complex.cos]
  ring_nf

