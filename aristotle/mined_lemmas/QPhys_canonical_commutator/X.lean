/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open Complex

/-- The position operator `X : f ↦ (x ↦ x · f x)` acting on complex-valued
functions of a real variable. -/

noncomputable def X (f : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * f x

/-- The momentum operator `P = -i ℏ d/dx` acting on complex-valued functions of a
real variable. -/
