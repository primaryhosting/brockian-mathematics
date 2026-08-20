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

lemma huckelLevelC3_two : huckelLevelC3 2 = -1 := by
  have h : (2 : ℝ) * Real.pi * (2 : ℕ) / 3 = 2 * Real.pi - (Real.pi - Real.pi / 3) := by
    push_cast; ring
  rw [huckelLevelC3, h, Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- The adjacency matrix of the cycle graph `C₃` is the all-ones matrix minus the identity. -/
