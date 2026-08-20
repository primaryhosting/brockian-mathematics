import Mathlib
/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the first command in a file, so the required
header comment is placed immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- The mass-squared operator (Hessian of the potential) at a field configuration `φ₀`:
the second derivative `D²V(φ₀)`, viewed as a continuous linear map sending a fluctuation
direction to the corresponding linear functional. In the physics normalization the mass
matrix of small fluctuations around `φ₀` is exactly this operator. -/

theorem differentiable_fderiv_of_contDiff_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {V : E → ℝ} (hV : ContDiff ℝ 2 V) :
    Differentiable ℝ (fun x => fderiv ℝ V x) :=
  (hV.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero

/-- **Goldstone's theorem** (classical field-theory form).

Setting: `E` is the space of field configurations, `V : E → ℝ` a `C²` potential, and
`φ₀` a ground state (a global minimum of `V`, i.e. the vacuum).

A continuous global symmetry acting on the theory gives a differentiable one-parameter
orbit `c : ℝ → E` through the vacuum (`c 0 = φ₀`) along which the potential is constant
(`V (c t) = V φ₀`), since the symmetry preserves `V`.

*Spontaneous breaking* means the vacuum is not invariant under the symmetry: the orbit
actually moves, i.e. its velocity `δ = c'(0)` at the vacuum is nonzero.

Conclusion: `δ` is a massless mode — a nonzero vector in the kernel of the mass-squared
operator `D²V(φ₀)`. Thus spontaneous breaking of a continuous global symmetry yields a
massless (Goldstone) boson. -/
