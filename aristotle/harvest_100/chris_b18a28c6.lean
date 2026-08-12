/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/
theorem integral_deriv_eq_zero_of_tendsto_zero
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Integrable f' volume)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0)) :
    ∫ x, f' x = 0 := by
  simpa using MeasureTheory.integral_of_hasDerivAt_of_tendsto hf hf' hbot htop

/-- Derivative of the "current" `ψ ψ'`. -/
theorem hasDerivAt_psi_mul_dpsi
    {psi dpsi ddpsi : ℝ → ℝ}
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x) (x : ℝ) :
    HasDerivAt (fun y => psi y * dpsi y) (dpsi x ^ 2 + psi x * ddpsi x) x := by
  have h := (hpsi x).mul (hdpsi x)
  convert h using 1
  ring

/-- Derivative of the virial function `Φ(x) = x (ψ'(x)² + (E - V(x)) ψ(x)²)`. -/
theorem hasDerivAt_virial_fun
    {psi dpsi ddpsi V dV : ℝ → ℝ} {E : ℝ}
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    (hSch : ∀ x, -ddpsi x + V x * psi x = E * psi x) (x : ℝ) :
    HasDerivAt (fun y => y * (dpsi y ^ 2 + (E - V y) * psi y ^ 2))
      (dpsi x ^ 2 + (E - V x) * psi x ^ 2 - x * dV x * psi x ^ 2) x := by
  have hdd : ddpsi x = (V x - E) * psi x := by
    have := hSch x; linarith [this]
  have d1 : HasDerivAt (fun y => dpsi y ^ 2) (2 * dpsi x * ddpsi x) x := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hdpsi x).pow 2
  have d2 : HasDerivAt (fun y => psi y ^ 2) (2 * psi x * dpsi x) x := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hpsi x).pow 2
  have d3 : HasDerivAt (fun y => E - V y) (-dV x) x := by
    simpa using (hasDerivAt_const x E).sub (hV x)
  have d4 := d3.mul d2
  have d5 := d1.add d4
  have d6 := (hasDerivAt_id x).mul d5
  convert d6 using 1
  simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  rw [hdd]
  ring

/-- **Quantum virial theorem** (one dimension, units `ħ² / 2m = 1`).

Let `psi` be a stationary state of the Schrödinger operator `H = -d²/dx² + V` with energy
`E`, i.e. `-ψ'' + V ψ = E ψ`, and assume the bound-state conditions: the kinetic density
`ψ'²`, the potential density `V ψ²`, the density `ψ²` and the virial density `x V'(x) ψ²`
are all integrable, and the boundary terms `ψ ψ'` and `x (ψ'² + (E - V) ψ²)` vanish at
`±∞`.  Then
`2 ⟨T⟩ = ⟨x · V'(x)⟩`,
the one-dimensional form of `2⟨T⟩ = ⟨r · ∇V⟩`. -/
theorem virial_theorem
    {psi dpsi ddpsi V dV : ℝ → ℝ} {E : ℝ}
    (hpsi : ∀ x, HasDerivAt psi (dpsi x) x)
    (hdpsi : ∀ x, HasDerivAt dpsi (ddpsi x) x)
    (hV : ∀ x, HasDerivAt V (dV x) x)
    (hSch : ∀ x, -ddpsi x + V x * psi x = E * psi x)
    (hT : Integrable (fun x => dpsi x ^ 2) volume)
    (hN : Integrable (fun x => psi x ^ 2) volume)
    (hVpsi : Integrable (fun x => V x * psi x ^ 2) volume)
    (hvir : Integrable (fun x => x * dV x * psi x ^ 2) volume)
    (hcur_bot : Tendsto (fun x => psi x * dpsi x) atBot (𝓝 0))
    (hcur_top : Tendsto (fun x => psi x * dpsi x) atTop (𝓝 0))
    (hvir_bot : Tendsto (fun x => x * (dpsi x ^ 2 + (E - V x) * psi x ^ 2)) atBot (𝓝 0))
    (hvir_top : Tendsto (fun x => x * (dpsi x ^ 2 + (E - V x) * psi x ^ 2)) atTop (𝓝 0)) :
    2 * ∫ x, dpsi x ^ 2 = ∫ x, x * dV x * psi x ^ 2 := by
  -- the two densities appearing as derivatives of the boundary functions
  set g₁ : ℝ → ℝ := fun x => dpsi x ^ 2 + (V x - E) * psi x ^ 2 with hg₁
  set g₂ : ℝ → ℝ := fun x => dpsi x ^ 2 + (E - V x) * psi x ^ 2 - x * dV x * psi x ^ 2
    with hg₂
  have hVE : Integrable (fun x => (V x - E) * psi x ^ 2) volume := by
    have : (fun x => (V x - E) * psi x ^ 2)
        = fun x => V x * psi x ^ 2 - E * psi x ^ 2 := by
      funext x; ring
    rw [this]
    exact hVpsi.sub (hN.const_mul E)
  have hg₁int : Integrable g₁ volume := hT.add hVE
  have hg₂int : Integrable g₂ volume := by
    have h : Integrable (fun x => dpsi x ^ 2 + (E - V x) * psi x ^ 2) volume := by
      have : (fun x => (E - V x) * psi x ^ 2)
          = fun x => -((V x - E) * psi x ^ 2) := by funext x; ring
      exact hT.add (this ▸ hVE.neg)
    exact h.sub hvir
  -- first integration by parts: derivative of `ψ ψ'`
  have h1 : ∫ x, g₁ x = 0 := by
    refine integral_deriv_eq_zero_of_tendsto_zero (f := fun y => psi y * dpsi y)
      ?_ hg₁int hcur_bot hcur_top
    intro x
    have h := hasDerivAt_psi_mul_dpsi hpsi hdpsi x
    have hdd : ddpsi x = (V x - E) * psi x := by have := hSch x; linarith
    convert h using 1
    rw [hg₁, hdd]; ring
  -- second integration by parts: derivative of the virial function
  have h2 : ∫ x, g₂ x = 0 :=
    integral_deriv_eq_zero_of_tendsto_zero
      (f := fun y => y * (dpsi y ^ 2 + (E - V y) * psi y ^ 2))
      (hasDerivAt_virial_fun hpsi hdpsi hV hSch) hg₂int hvir_bot hvir_top
  -- add them up
  have hsum : ∫ x, (g₁ x + g₂ x) = 0 := by
    rw [integral_add hg₁int hg₂int, h1, h2, add_zero]
  have hpt : (fun x => g₁ x + g₂ x)
      = fun x => 2 * dpsi x ^ 2 - x * dV x * psi x ^ 2 := by
    funext x; rw [hg₁, hg₂]; ring
  rw [hpt, integral_sub (hT.const_mul 2) hvir, integral_const_mul] at hsum
  linarith

/-! ### Non-vacuity: the harmonic-oscillator ground state

The hypotheses of `Phys.virial_theorem` are satisfiable: the ground state
`ψ(x) = exp (-x²/2)` of the harmonic oscillator `V(x) = x²` with energy `E = 1`
satisfies all of them, and is not the zero function. -/

/-- Ground state of the harmonic oscillator (unnormalized). -/
noncomputable def hoPsi : ℝ → ℝ := fun x => Real.exp (-x ^ 2 / 2)

/-- Its first derivative. -/
noncomputable def hoDPsi : ℝ → ℝ := fun x => -x * Real.exp (-x ^ 2 / 2)

/-- Its second derivative. -/
noncomputable def hoDDPsi : ℝ → ℝ := fun x => (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)

/-- The harmonic potential. -/
def hoV : ℝ → ℝ := fun x => x ^ 2

/-- Its derivative. -/
def hoDV : ℝ → ℝ := fun x => 2 * x

theorem hoPsi_sq (x : ℝ) : hoPsi x ^ 2 = Real.exp (-x ^ 2) := by
  rw [hoPsi, sq, ← Real.exp_add]; ring_nf

theorem hasDerivAt_hoPsi (x : ℝ) : HasDerivAt hoPsi (hoDPsi x) x := by
  have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have h2 := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert h2 using 1
    simp; ring
  have h3 := h.exp
  convert h3 using 1
  rw [hoDPsi]; ring

theorem hasDerivAt_hoDPsi (x : ℝ) : HasDerivAt hoDPsi (hoDDPsi x) x := by
  have h := ((hasDerivAt_id x).neg).mul (hasDerivAt_hoPsi x)
  convert h using 1
  rw [hoDDPsi, hoDPsi]
  simp only [Pi.neg_apply, id_eq, hoPsi]
  ring

theorem hasDerivAt_hoV (x : ℝ) : HasDerivAt hoV (hoDV x) x := by
  have h := hasDerivAt_pow 2 x
  convert h using 1
  rw [hoDV]; simp

theorem tendsto_mul_exp_neg_sq_atTop :
    Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  refine squeeze_zero_norm' ?_ (by simpa using h)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hle : Real.exp (-x ^ 2) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.2; nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx0, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left hle hx0

theorem tendsto_mul_exp_neg_sq_atBot :
    Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := (tendsto_mul_exp_neg_sq_atTop.neg).comp tendsto_neg_atBot_atTop
  have he : ((fun x : ℝ => -(x * Real.exp (-x ^ 2))) ∘ (fun x : ℝ => -x))
      = fun x : ℝ => x * Real.exp (-x ^ 2) := by
    funext x; simp [Function.comp]
  rw [he] at h
  simpa using h

theorem integrable_exp_neg_sq : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) volume := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem integrable_sq_mul_exp_neg_sq :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) volume := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := 2) one_pos (by norm_num)

/-- **Non-vacuity of `Phys.virial_theorem`.**  All of its hypotheses hold for the
harmonic-oscillator ground state `ψ(x) = exp (-x²/2)`, `V(x) = x²`, `E = 1`, which is a
nonzero state. -/
theorem virial_hypotheses_nonvacuous :
    (∀ x, HasDerivAt hoPsi (hoDPsi x) x) ∧
    (∀ x, HasDerivAt hoDPsi (hoDDPsi x) x) ∧
    (∀ x, HasDerivAt hoV (hoDV x) x) ∧
    (∀ x, -hoDDPsi x + hoV x * hoPsi x = 1 * hoPsi x) ∧
    Integrable (fun x => hoDPsi x ^ 2) volume ∧
    Integrable (fun x => hoPsi x ^ 2) volume ∧
    Integrable (fun x => hoV x * hoPsi x ^ 2) volume ∧
    Integrable (fun x => x * hoDV x * hoPsi x ^ 2) volume ∧
    Tendsto (fun x => hoPsi x * hoDPsi x) atBot (𝓝 0) ∧
    Tendsto (fun x => hoPsi x * hoDPsi x) atTop (𝓝 0) ∧
    Tendsto (fun x => x * (hoDPsi x ^ 2 + (1 - hoV x) * hoPsi x ^ 2)) atBot (𝓝 0) ∧
    Tendsto (fun x => x * (hoDPsi x ^ 2 + (1 - hoV x) * hoPsi x ^ 2)) atTop (𝓝 0) ∧
    hoPsi ≠ 0 := by
  have hdsq : ∀ x : ℝ, hoDPsi x ^ 2 = x ^ 2 * Real.exp (-x ^ 2) := by
    intro x
    have hx : hoDPsi x = -x * hoPsi x := rfl
    rw [hx, mul_pow, hoPsi_sq]
    ring
  have hcur : ∀ x : ℝ, hoPsi x * hoDPsi x = -(x * Real.exp (-x ^ 2)) := by
    intro x
    have hx : hoDPsi x = -x * hoPsi x := rfl
    rw [hx, show hoPsi x * (-x * hoPsi x) = -(x * hoPsi x ^ 2) by ring, hoPsi_sq]
  have hPhi : ∀ x : ℝ, x * (hoDPsi x ^ 2 + (1 - hoV x) * hoPsi x ^ 2)
      = x * Real.exp (-x ^ 2) := by
    intro x
    rw [hdsq, hoPsi_sq, hoV]
    ring
  refine ⟨hasDerivAt_hoPsi, hasDerivAt_hoDPsi, hasDerivAt_hoV, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x; rw [hoDDPsi, hoV, hoPsi]; ring
  · exact (integrable_congr (Filter.Eventually.of_forall hdsq)).2 integrable_sq_mul_exp_neg_sq
  · exact (integrable_congr (Filter.Eventually.of_forall hoPsi_sq)).2 integrable_exp_neg_sq
  · refine (integrable_congr (Filter.Eventually.of_forall (fun x => ?_))).2
      integrable_sq_mul_exp_neg_sq
    rw [hoV, hoPsi_sq]
  · refine (integrable_congr (Filter.Eventually.of_forall (fun x => ?_))).2
      (integrable_sq_mul_exp_neg_sq.const_mul 2)
    rw [hoDV, hoPsi_sq]; ring
  · simpa [hcur] using tendsto_mul_exp_neg_sq_atBot.neg
  · simpa [hcur] using tendsto_mul_exp_neg_sq_atTop.neg
  · simpa [hPhi] using tendsto_mul_exp_neg_sq_atBot
  · simpa [hPhi] using tendsto_mul_exp_neg_sq_atTop
  · intro h
    have h0 := congrFun h 0
    simp [hoPsi] at h0

/-- The virial theorem applied to the harmonic-oscillator ground state. -/
theorem virial_harmonic_oscillator :
    2 * ∫ x : ℝ, hoDPsi x ^ 2 = ∫ x : ℝ, x * hoDV x * hoPsi x ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ :=
    virial_hypotheses_nonvacuous
  exact virial_theorem h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

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

