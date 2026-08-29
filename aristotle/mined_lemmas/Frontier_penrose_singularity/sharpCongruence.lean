/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The focusing mechanism behind the Penrose singularity theorem

The physical content of the Penrose singularity theorem is the *focusing* of a null geodesic
congruence.  Along a null geodesic congruence with vanishing twist (such as the family of null
geodesics orthogonal to a closed codimension-two surface), the expansion `θ` of the congruence,
as a function of the affine parameter `t`, obeys the Raychaudhuri equation

  `θ' = - θ² / 2 - σ_{ab} σ^{ab} - Ric(k, k)`

in four spacetime dimensions.  The shear term `σ_{ab} σ^{ab}` is nonnegative, and the null energy
condition gives `Ric(k, k) ≥ 0` (via the Einstein equations, `Ric(k,k) = 8π T(k,k) ≥ 0` for a null
vector `k`).  Hence the *Raychaudhuri inequality*

  `θ' ≤ - θ² / 2`

holds along every generator.  A *trapped surface* is by definition a closed codimension-two
surface whose two null normal congruences both have strictly negative initial expansion,
`θ 0 < 0`.

The content formalized below is the resulting incompleteness: an affinely parametrized generator
of such a congruence cannot be extended to arbitrarily large affine parameter; in fact its affine
length is at most `-2 / θ 0`.  This is the analytic heart of the Penrose theorem (the remaining
ingredients of Penrose's argument are the global causal-theoretic ones, which turn the finiteness
of the affine length into the statement that the boundary of the future of the trapped surface is
compact and hence that the spacetime cannot be null geodesically complete).
-/

/-- The analytic datum attached to a generator of a null geodesic congruence with vanishing
twist: its expansion `theta`, as a function of the affine parameter, together with a derivative
`theta'`, defined for affine parameter in `[0, length)`, where `length ∈ ℝ≥0∞` is the affine
length of the maximal extension of the generator (so `length = ⊤` means the generator is future
affinely complete). The field `raychaudhuri` records the Raychaudhuri inequality
`θ' ≤ -θ²/2`, which holds for a twist-free null congruence in a spacetime satisfying the null
energy condition. -/
structure NullCongruence where
  /-- Affine length of the maximal future extension of the generator. -/
  length : ℝ≥0∞
  /-- The expansion of the congruence as a function of the affine parameter. -/
  theta : ℝ → ℝ
  /-- The derivative of the expansion. -/
  theta' : ℝ → ℝ
  /-- `theta'` really is the derivative of `theta` along the generator. -/
  hasDeriv : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < length → HasDerivAt theta (theta' t) t
  /-- Raychaudhuri's equation together with the null energy condition (`Ric(k,k) ≥ 0`) and the
  nonnegativity of the shear squared. -/
  raychaudhuri : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < length → theta' t ≤ -(theta t) ^ 2 / 2

namespace NullCongruence

variable (C : NullCongruence)

/-- The generator emanates from a *trapped* surface: the initial expansion is negative. -/

noncomputable def sharpCongruence : NullCongruence where
  length := 1
  theta := fun t => 2 / (t - 1)
  theta' := fun t => -2 / (t - 1) ^ 2
  hasDeriv := by
    intro t _ ht
    have ht1 : t < 1 := ENNReal.ofReal_lt_one.mp ht
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have hne : t - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
    have h2 := (h1.inv hne).const_mul (2 : ℝ)
    have hfun : (fun y : ℝ => 2 * ((fun s : ℝ => s - 1)⁻¹ y)) = fun s : ℝ => 2 / (s - 1) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun] at h2
    convert h2 using 1
    ring
  raychaudhuri := by
    intro t _ ht
    have ht1 : t < 1 := ENNReal.ofReal_lt_one.mp ht
    have hne : t - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
    have hpos : 0 < (t - 1) ^ 2 := by positivity
    have heq : -(2 / (t - 1)) ^ 2 / 2 = -2 / (t - 1) ^ 2 := by
      field_simp
    rw [heq]

/-- The extremal generator does issue from a trapped surface. -/
