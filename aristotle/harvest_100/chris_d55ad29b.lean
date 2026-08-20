import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Noether identity.**  If the potential `V` (with gradient field `G`) is invariant under a
one-parameter flow `Φ` whose infinitesimal generator is `K` (i.e. `Φ 0 = id` and
`(d/dt) Φ t x |_{t=0} = K x`), then the gradient of `V` is everywhere orthogonal to the
direction of the symmetry orbit. -/
theorem inner_gradient_generator_eq_zero
    {V : E → ℝ} {G : E → E} {K : E →L[ℝ] E} {Φ : ℝ → E → E}
    (hV : ∀ x, HasFDerivAt V (innerSL ℝ (G x)) x)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hgen : ∀ x, HasDerivAt (fun t => Φ t x) (K x) 0)
    (hinv : ∀ t x, V (Φ t x) = V x) (x : E) :
    ⟪G x, K x⟫ = 0 := by
  have hVx : HasFDerivAt V (innerSL ℝ (G x)) (Φ 0 x) := by rw [hΦ0 x]; exact hV x
  have hcomp : HasDerivAt (fun t => V (Φ t x)) (⟪G x, K x⟫) 0 := by
    simpa [Function.comp] using hVx.comp_hasDerivAt 0 (hgen x)
  have hconst : HasDerivAt (fun t => V (Φ t x)) 0 0 := by
    simpa [hinv] using (hasDerivAt_const (0 : ℝ) (V x))
  exact hcomp.unique hconst

/-- **Goldstone's theorem.**

Setting: a potential `V` on a real inner product space `E`, with gradient field `G`
(`hV`) and Hessian `H` at the vacuum `v` (`hH`, the derivative of the gradient field);
the Hessian is symmetric (`hHsymm`, Clairaut/Schwarz).  The potential is invariant under a
continuous one-parameter group of symmetries `Φ` with infinitesimal generator `K`
(`hΦ0`, `hgen`, `hinv`).  The point `v` is a vacuum, i.e. a stationary point of `V` (`hvac`),
and the symmetry is *spontaneously broken* at `v`: the vacuum is not invariant, its orbit
direction `K v` is nonzero (`hbroken`).

Conclusion: the mass matrix `H` (the Hessian of the potential at the vacuum) has a nonzero
kernel vector, i.e. there is a massless mode — the Goldstone boson.  Indeed the massless
direction is exactly the broken symmetry direction `K v`. -/
theorem goldstone
    {V : E → ℝ} {G : E → E} {K H : E →L[ℝ] E} {Φ : ℝ → E → E} {v : E}
    (hV : ∀ x, HasFDerivAt V (innerSL ℝ (G x)) x)
    (hH : HasFDerivAt G H v)
    (hHsymm : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hgen : ∀ x, HasDerivAt (fun t => Φ t x) (K x) 0)
    (hinv : ∀ t x, V (Φ t x) = V x)
    (hvac : G v = 0)
    (hbroken : K v ≠ 0) :
    ∃ u : E, u ≠ 0 ∧ H u = 0 := by
  refine ⟨K v, hbroken, ?_⟩
  -- The Noether identity `⟪G x, K x⟫ = 0` holds identically; differentiate it at `v`.
  have hnoether : ∀ x, ⟪G x, K x⟫ = 0 :=
    inner_gradient_generator_eq_zero hV hΦ0 hgen hinv
  have hK : HasFDerivAt (fun x => K x) K v := K.hasFDerivAt
  have hd := hH.inner ℝ hK
  have hd0 : HasFDerivAt (fun x => ⟪G x, K x⟫) (0 : E →L[ℝ] ℝ) v := by
    simpa [hnoether] using (hasFDerivAt_const (0 : ℝ) v)
  have hker : ∀ w : E, ⟪H w, K v⟫ = 0 := by
    intro w
    have := congrArg (fun L : E →L[ℝ] ℝ => L w) (hd.unique hd0)
    simpa [hvac, real_inner_comm] using this
  -- Symmetry of the Hessian turns this into `H (K v) = 0`.
  have : ⟪H (K v), H (K v)⟫ = 0 := by
    rw [hHsymm (K v) (H (K v)), real_inner_comm]
    exact hker (H (K v))
  exact inner_self_eq_zero.mp this

/-!
## Non-vacuity: the Mexican-hat potential with a `U(1)` symmetry

The hypotheses of `Phys.goldstone` are satisfiable in the standard physical example: the complex
plane `ℂ` (viewed as a two-dimensional real inner product space) with the Mexican-hat potential
`V z = (|z|² - 1)²`, invariant under the `U(1)` rotations `z ↦ e^{it} z`, and the vacuum `z = 1`.
The broken generator is `z ↦ i z`, and the corresponding massless mode is the phase direction `i`.
-/

namespace MexicanHat

/-- The Mexican-hat potential `V z = (|z|² - 1)²`. -/
noncomputable def V : ℂ → ℝ := fun z => (⟪z, z⟫ - 1) ^ 2

/-- The gradient field of the Mexican-hat potential. -/
noncomputable def grad : ℂ → ℂ := fun z => (4 * (⟪z, z⟫ - 1)) • z

/-- The infinitesimal generator of the `U(1)` symmetry: `z ↦ i z`. -/
noncomputable def gen : ℂ →L[ℝ] ℂ := Complex.I • (ContinuousLinearMap.id ℝ ℂ)

/-- The Hessian (mass matrix) of the Mexican-hat potential at the vacuum `z = 1`. -/
noncomputable def hess : ℂ →L[ℝ] ℂ := (8 : ℝ) • ((innerSL ℝ (1 : ℂ)).smulRight (1 : ℂ))

/-- The `U(1)` flow `z ↦ e^{it} z`. -/
noncomputable def flow : ℝ → ℂ → ℂ := fun t z => Complex.exp (t * Complex.I) * z

theorem hasFDerivAt_normSq (z : ℂ) :
    HasFDerivAt (fun x : ℂ => ⟪x, x⟫) ((2 : ℝ) • innerSL ℝ z) z := by
  have h := (hasFDerivAt_id z).inner ℝ (hasFDerivAt_id z)
  convert h using 1
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, id_eq, real_inner_comm w z]
  ring

theorem hasFDerivAt_V (z : ℂ) : HasFDerivAt V (innerSL ℝ (grad z)) z := by
  have h := (((hasFDerivAt_normSq z).sub_const 1).pow 2)
  convert h using 1
  ext w
  simp only [grad, innerSL_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem hasFDerivAt_grad : HasFDerivAt grad hess 1 := by
  have h1 : HasFDerivAt (fun x : ℂ => 4 * (⟪x, x⟫ - 1))
      ((4 : ℝ) • ((2 : ℝ) • innerSL ℝ (1 : ℂ))) (1 : ℂ) := by
    simpa using (((hasFDerivAt_normSq 1).sub_const 1).const_mul (4 : ℝ))
  have h2 := h1.smul (hasFDerivAt_id (1 : ℂ))
  convert h2 using 1
  ext w
  have h3 : ⟪(1 : ℂ), (1 : ℂ)⟫ = (1 : ℝ) := by simp
  simp only [hess, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul, h3, id_eq, sub_self, mul_zero, zero_smul, zero_add,
    smul_smul]
  ring_nf

theorem hess_symm (x y : ℂ) : ⟪hess x, y⟫ = ⟪x, hess y⟫ := by
  simp only [hess, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm x 1]
  ring

theorem flow_zero (z : ℂ) : flow 0 z = z := by simp [flow]

theorem hasDerivAt_flow (z : ℂ) : HasDerivAt (fun t : ℝ => flow t z) (gen z) 0 := by
  have h : HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I)) Complex.I 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).cexp
    simpa using this
  simpa [flow, gen] using h.mul_const z

theorem V_flow (t : ℝ) (z : ℂ) : V (flow t z) = V z := by
  simp only [V, flow, real_inner_self_eq_norm_sq, norm_mul, Complex.norm_exp]
  simp

theorem grad_vacuum : grad 1 = 0 := by simp [grad]

theorem gen_vacuum_ne_zero : gen 1 ≠ 0 := by simp [gen, Complex.I_ne_zero]

/-- The Mexican-hat model really does have a massless mode, by `Phys.goldstone`. -/
theorem goldstone_boson : ∃ u : ℂ, u ≠ 0 ∧ hess u = 0 :=
  Phys.goldstone hasFDerivAt_V hasFDerivAt_grad hess_symm flow_zero hasDerivAt_flow V_flow
    grad_vacuum gen_vacuum_ne_zero

end MexicanHat

end Phys

import Mathlib

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
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

