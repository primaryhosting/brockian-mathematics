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

noncomputable def massOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (φ₀ : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  fderiv ℝ (fun x => fderiv ℝ V x) φ₀

/-- A direction `δ` is a *massless mode* of the potential `V` at `φ₀` when it is a nonzero
vector annihilated by the mass-squared operator, i.e. a nonzero element of the kernel of the
Hessian: fluctuations along `δ` cost no quadratic energy. -/

def IsMasslessMode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (φ₀ : E) (δ : E) : Prop :=
  δ ≠ 0 ∧ massOperator V φ₀ δ = 0

/-- Along a symmetry orbit through a minimum, every point is again a minimum, hence a
critical point of the potential. -/

theorem fderiv_eq_zero_along_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} {φ₀ : E} {c : ℝ → E}
    (hmin : ∀ x, V φ₀ ≤ V x) (horbit : ∀ t, V (c t) = V φ₀) (t : ℝ) :
    fderiv ℝ V (c t) = 0 := by
  have : IsLocalMin V (c t) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [horbit t]
    exact hmin x
  exact this.fderiv_eq_zero

/-- The potential is twice continuously differentiable, so its differential is differentiable. -/

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

theorem goldstone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} {φ₀ : E} {c : ℝ → E}
    (hV : ContDiff ℝ 2 V)
    (hmin : ∀ x, V φ₀ ≤ V x)
    (hc : Differentiable ℝ c) (hc0 : c 0 = φ₀)
    (horbit : ∀ t, V (c t) = V φ₀)
    (hbroken : deriv c 0 ≠ 0) :
    IsMasslessMode V φ₀ (deriv c 0) := by
  refine ⟨hbroken, ?_⟩
  set g : E → (E →L[ℝ] ℝ) := fun x => fderiv ℝ V x with hg
  have hgdiff : Differentiable ℝ g := differentiable_fderiv_of_contDiff_two hV
  have hzero : ∀ t, g (c t) = 0 := fun t => fderiv_eq_zero_along_orbit hmin horbit t
  have h1 : HasDerivAt (fun t => g (c t)) ((fderiv ℝ g (c 0)) (deriv c 0)) 0 := by
    simpa using (hgdiff (c 0)).hasFDerivAt.comp_hasDerivAt 0 (hc 0).hasDerivAt
  have h2 : HasDerivAt (fun t => g (c t)) 0 0 := by
    simp only [hzero]
    exact hasDerivAt_const 0 0
  have := h1.unique h2
  rw [massOperator, ← hc0]
  exact this

/-- Restatement: under spontaneous breaking of a continuous symmetry there *exists* a
massless mode. -/
