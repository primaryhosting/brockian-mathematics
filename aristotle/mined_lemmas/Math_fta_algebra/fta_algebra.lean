/- Note: Lean requires `import` to be the first command, and a `/-! -/` module
docstring counts as a command, so the requested header is reproduced verbatim
inside a plain (nestable) comment here, and repeated as a module docstring below.

/-!
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root.
Here "nonconstant" is expressed as `0 < p.degree`. This is `Complex.exists_root` in Mathlib. -/

theorem fta_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) : ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root hp

/-- Variant of the fundamental theorem of algebra phrased with `natDegree`. -/
