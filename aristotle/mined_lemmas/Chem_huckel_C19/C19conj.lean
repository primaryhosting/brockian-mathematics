/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

noncomputable def C19conj : Matrix (ZMod 19) (ZMod 19) ℂ := fun k j => om ^ (18 * (k.val * j.val))

/-! ### Basic facts about the root of unity -/

