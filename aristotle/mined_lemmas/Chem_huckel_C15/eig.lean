/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Matrix

/-- A primitive 15-th root of unity. -/

noncomputable def eig (k : Fin 15) : ℂ := ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ)

