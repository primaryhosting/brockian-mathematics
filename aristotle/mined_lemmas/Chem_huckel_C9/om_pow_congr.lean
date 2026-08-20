import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem om_pow_congr {a b : ℕ} (h : a % 9 = b % 9) : om ^ a = om ^ b := by
  rw [← om_pow_mod a, ← om_pow_mod b, h]

