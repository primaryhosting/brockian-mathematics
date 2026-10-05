/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open scoped Real
open Finset

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A primitive 17-th root of unity. -/

def adjC17 : Matrix (ZMod 17) (ZMod 17) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

