/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma zeta_pow_mul_thirteen (k : ℕ) : zeta ^ (k * 13) = zeta ^ (k * 5) :=
  zeta_pow_mod _ _ (by omega)

