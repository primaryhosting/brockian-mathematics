/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to be the first command, so the header above is a plain
-- block comment; the identical module docstring is repeated below.)

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## The complexified Lorentz group

The mathematical heart of the CPT theorem (Jost's theorem) is the following fact: the total
inversion `-1` of Minkowski spacetime, which is *not* in the identity component of the real
Lorentz group, *is* reachable inside the **complex** Lorentz group `L(ℂ) = O(1,3;ℂ)`.  Indeed

  `diag(-1,-1,-1,-1) = diag(-1,-1,1,1) · diag(1,1,-1,-1)`,

where the second factor is the real rotation by `π` about the `x`-axis (an element of the
proper orthochronous group `L₊↑`) and the first factor is the value at rapidity `iπ` of the
family of boosts in the `(0,1)`–plane analytically continued to imaginary rapidity.

This is why a Lorentz-invariant theory whose Wightman functions possess the standard analytic
continuation in the boost parameter is automatically invariant under total inversion. -/

/-- The Minkowski metric `diag(1,-1,-1,-1)` on complexified spacetime `ℂ⁴`. -/

theorem imagBoost_zero : imagBoost 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [imagBoost, boost01]

/-- At imaginary rapidity `iπ` the boost becomes `diag(-1,-1,1,1)`: it inverts time together
with the `x`-axis. -/
