/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset Real

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/

noncomputable def gibbsEntropy {ι : Type*} [Fintype ι] (k : ℝ) (p : ι → ℝ) : ℝ :=
  -k * ∑ i, p i * Real.log (p i)

/-- The mean energy `∑ pᵢ Eᵢ` of a statistical state `p` with energy levels `E`. -/
