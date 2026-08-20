/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Complex

/-- The primitive 18-th root of unity `exp(2πi/18)`. -/

lemma om_pow_injOn {i j : ℕ} (hi : i < 18) (hj : j < 18) (h : om ^ i = om ^ j) : i = j :=
  om_primitive.pow_inj hi hj h

/-- The DFT / Vandermonde matrix built from powers of `om`. -/
