/-
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity, `ω = exp(2πi/5)`. -/

noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character on `ZMod 5`, `e k = ω ^ k`. -/
