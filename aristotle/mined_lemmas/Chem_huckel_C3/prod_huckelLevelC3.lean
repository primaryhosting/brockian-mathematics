/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Real Matrix SimpleGraph

namespace Chem

/-- The Hückel level of the `k`-th molecular orbital of the cyclic `C₃` system,
in units of the resonance integral `β` (relative to `α`): `2 cos (2πk/3)`. -/

lemma prod_huckelLevelC3 :
    ∏ k ∈ Finset.range 3, (X - C (huckelLevelC3 k)) = (X ^ 3 - 3 * X - 2 : ℝ[X]) := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, huckelLevelC3_zero, huckelLevelC3_one, huckelLevelC3_two]
  simp only [map_neg, map_one, map_ofNat]
  ring

/-- The three Hückel levels of `C₃`, in raw form. -/
