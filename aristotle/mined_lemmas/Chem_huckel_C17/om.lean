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

noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)

