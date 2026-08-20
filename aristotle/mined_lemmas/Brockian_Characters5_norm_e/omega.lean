/-
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/

noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e k = ω ^ k.val`. -/
