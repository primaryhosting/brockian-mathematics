import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

noncomputable def C10G : Matrix (ZMod 10) (ZMod 10) ℂ :=
  Matrix.of fun k j => chi (-(k * j)) / 10

