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

theorem imagBoost_pi_spaceRotationPi_mulVec (v : Fin 4 → ℂ) :
    imagBoost π *ᵥ (spaceRotationPi.map (fun a : ℝ => (a : ℂ)) *ᵥ v) = -v := by
  rw [Matrix.mulVec_mulVec, imagBoost_pi_mul_spaceRotationPi, Matrix.neg_mulVec,
    Matrix.one_mulVec]

/-! ### Jost's lemma: `-1` lies in the identity component of `L₊(ℂ)`

The factorisation above is the computational core.  The following two results record its
geometric meaning: the total inversion is a proper complex Lorentz transformation, and it is
connected to the identity *inside* the complex Lorentz group — which is false for the real
Lorentz group. -/

/-- The `(0,1)`–boost and `(2,3)`–rotation combined into a single one-parameter family, used
to connect `1` to `-1` inside `L₊(ℂ)`. -/
