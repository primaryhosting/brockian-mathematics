import RequestProject.Main

/-!
# A concrete instance of the virial theorem

The hypotheses of `Phys.virial_theorem` are satisfiable: we check them for the
ground state `ψ(x) = π^(-1/4) exp(-x²/2)` of the harmonic oscillator
`V(x) = x²/2`, with energy `E = 1/2`, and deduce the virial identity
`2⟨T⟩ = ⟨x ∂ₓV⟩ = 2⟨V⟩` for that state.
-/

namespace Phys

open MeasureTheory Filter Topology Real

/-- `exp (-x²/2)` squared is `exp (-x²)`. -/
theorem exp_neg_half_sq_sq (x : ℝ) : (Real.exp (-x ^ 2 / 2)) ^ 2 = Real.exp (-x ^ 2) := by
  rw [sq, ← Real.exp_add]
  ring_nf

/-- A uniform bound for `|x|ⁿ exp (-x²/2)`. -/
theorem abs_pow_mul_exp_neg_half_sq_le (n : ℕ) (x : ℝ) :
    |x| ^ n * Real.exp (-x ^ 2 / 2) ≤ 1 + 2 ^ n * (Nat.factorial n : ℝ) := by
  have hexp_pos : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
  have hexp_le_one : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  -- `|x|ⁿ ≤ 1 + (x²)ⁿ`
  have hxn : |x| ^ n ≤ 1 + (x ^ 2) ^ n := by
    rcases le_or_gt |x| 1 with h | h
    · have : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg x) h
      nlinarith [pow_nonneg (sq_nonneg x) n]
    · have h1 : |x| ^ n ≤ (|x| ^ 2) ^ n :=
        pow_le_pow_left₀ (abs_nonneg x) (by nlinarith) n
      have h2 : (|x| ^ 2) ^ n = (x ^ 2) ^ n := by rw [sq_abs]
      nlinarith [h1, h2]
  -- `(x²)ⁿ ≤ 2ⁿ n! exp (x²/2)`
  have hfac : (x ^ 2) ^ n ≤ 2 ^ n * (Nat.factorial n : ℝ) * Real.exp (x ^ 2 / 2) := by
    have h := Real.pow_div_factorial_le_exp (x ^ 2 / 2) (by positivity) n
    have hfac_pos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have h' : (x ^ 2 / 2) ^ n ≤ (Nat.factorial n : ℝ) * Real.exp (x ^ 2 / 2) := by
      rw [div_le_iff₀ hfac_pos] at h
      linarith [h]
    have hpow : (x ^ 2) ^ n = 2 ^ n * (x ^ 2 / 2) ^ n := by
      rw [div_pow, ← mul_div_assoc]
      field_simp
    rw [hpow]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith [h']
  have hmul : Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show x ^ 2 / 2 + -x ^ 2 / 2 = 0 by ring, Real.exp_zero]
  calc |x| ^ n * Real.exp (-x ^ 2 / 2)
      ≤ (1 + 2 ^ n * (Nat.factorial n : ℝ) * Real.exp (x ^ 2 / 2)) * Real.exp (-x ^ 2 / 2) := by
        have := hxn.trans (by linarith [hfac] : 1 + (x ^ 2) ^ n
          ≤ 1 + 2 ^ n * (Nat.factorial n : ℝ) * Real.exp (x ^ 2 / 2))
        exact mul_le_mul_of_nonneg_right this hexp_pos.le
    _ = Real.exp (-x ^ 2 / 2) + 2 ^ n * (Nat.factorial n : ℝ) := by
        rw [add_mul, one_mul, mul_assoc, hmul, mul_one]
    _ ≤ 1 + 2 ^ n * (Nat.factorial n : ℝ) := by linarith

/-- `xⁿ exp (-x²)` is integrable on the line. -/
theorem integrable_pow_mul_gaussian (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) volume := by
  have hbase : Integrable (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ n * Real.exp (-x ^ 2 / 2)) volume := by
    fun_prop
  have hbdd : Integrable
      (fun x : ℝ => (x ^ n * Real.exp (-x ^ 2 / 2)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) volume := by
    refine hbase.bdd_mul (c := 1 + 2 ^ n * (Nat.factorial n : ℝ)) hmeas ?_
    filter_upwards with x
    have h := abs_pow_mul_exp_neg_half_sq_le n x
    have : ‖x ^ n * Real.exp (-x ^ 2 / 2)‖ = |x| ^ n * Real.exp (-x ^ 2 / 2) := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
        abs_of_pos (Real.exp_pos _)]
    rw [this]
    exact h
  refine hbdd.congr ?_
  filter_upwards with x
  have h : Real.exp (-x ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) = Real.exp (-x ^ 2) := by
    rw [← Real.exp_add]
    ring_nf
  calc x ^ n * Real.exp (-x ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)
      = x ^ n * (Real.exp (-x ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by ring
    _ = x ^ n * Real.exp (-x ^ 2) := by rw [h]

/-- `exp (-x²/2) → 0` at `+∞`. -/
theorem tendsto_exp_neg_half_sq_atTop :
    Tendsto (fun x : ℝ => Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop := by
    apply Filter.Tendsto.atTop_div_const (by norm_num)
    exact tendsto_pow_atTop (by norm_num)
  exact (tendsto_neg_atBot_iff.mpr h1).congr fun x => by ring

/-- `exp (-x²/2) → 0` at `-∞`. -/
theorem tendsto_exp_neg_half_sq_atBot :
    Tendsto (fun x : ℝ => Real.exp (-x ^ 2 / 2)) atBot (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atBot atTop := by
    apply Filter.Tendsto.atTop_div_const (by norm_num)
    exact tendsto_pow_atBot_atTop_of_even (by decide)
  exact (tendsto_neg_atBot_iff.mpr h1).congr fun x => by ring

/-- `xⁿ exp (-x²) → 0` at `+∞`. -/
theorem tendsto_pow_mul_gaussian_atTop (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  have hbound : ∀ x : ℝ, ‖x ^ n * Real.exp (-x ^ 2)‖
      ≤ (1 + 2 ^ n * (Nat.factorial n : ℝ)) * Real.exp (-x ^ 2 / 2) := by
    intro x
    have h := abs_pow_mul_exp_neg_half_sq_le n x
    have hsplit : Real.exp (-x ^ 2) = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hnorm : ‖x ^ n * Real.exp (-x ^ 2)‖
        = (|x| ^ n * Real.exp (-x ^ 2 / 2)) * Real.exp (-x ^ 2 / 2) := by
      rw [hsplit, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
        abs_of_pos (by positivity : (0:ℝ) < Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2))]
      ring
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hlim : Tendsto (fun x : ℝ => (1 + 2 ^ n * (Nat.factorial n : ℝ)) * Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    simpa using tendsto_exp_neg_half_sq_atTop.const_mul (1 + 2 ^ n * (Nat.factorial n : ℝ))
  exact squeeze_zero_norm (fun x => hbound x) hlim

/-- `xⁿ exp (-x²) → 0` at `-∞`. -/
theorem tendsto_pow_mul_gaussian_atBot (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have hbound : ∀ x : ℝ, ‖x ^ n * Real.exp (-x ^ 2)‖
      ≤ (1 + 2 ^ n * (Nat.factorial n : ℝ)) * Real.exp (-x ^ 2 / 2) := by
    intro x
    have h := abs_pow_mul_exp_neg_half_sq_le n x
    have hsplit : Real.exp (-x ^ 2) = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hnorm : ‖x ^ n * Real.exp (-x ^ 2)‖
        = (|x| ^ n * Real.exp (-x ^ 2 / 2)) * Real.exp (-x ^ 2 / 2) := by
      rw [hsplit, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
        abs_of_pos (by positivity : (0:ℝ) < Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2))]
      ring
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hlim : Tendsto (fun x : ℝ => (1 + 2 ^ n * (Nat.factorial n : ℝ)) * Real.exp (-x ^ 2 / 2)) atBot (𝓝 0) := by
    simpa using tendsto_exp_neg_half_sq_atBot.const_mul (1 + 2 ^ n * (Nat.factorial n : ℝ))
  exact squeeze_zero_norm (fun x => hbound x) hlim

/-- Normalization constant `π^(-1/4)` of the harmonic-oscillator ground state. -/
noncomputable def hoC : ℝ := Real.sqrt (1 / Real.sqrt Real.pi)

theorem hoC_sq : hoC ^ 2 = 1 / Real.sqrt Real.pi := by
  rw [hoC, Real.sq_sqrt]
  positivity

/-- Ground state of the harmonic oscillator. -/
noncomputable def hoPsi (x : ℝ) : ℝ := hoC * Real.exp (-x ^ 2 / 2)

/-- Its first derivative. -/
noncomputable def hoDPsi (x : ℝ) : ℝ := -(hoC * x * Real.exp (-x ^ 2 / 2))

/-- Its second derivative. -/
noncomputable def hoDDPsi (x : ℝ) : ℝ := hoC * (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)

/-- The harmonic potential. -/
noncomputable def hoV (x : ℝ) : ℝ := x ^ 2 / 2

/-- Its derivative. -/
noncomputable def hoDV (x : ℝ) : ℝ := x

/-- The derivative of `t ↦ -t²/2`. -/
theorem hasDerivAt_neg_half_sq (x : ℝ) : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-x) x := by
  have h := ((hasDerivAt_id x).pow 2).neg.div_const 2
  refine h.congr_deriv ?_
  simp
  ring

theorem hasDerivAt_hoPsi (x : ℝ) : HasDerivAt hoPsi (hoDPsi x) x := by
  have h := ((hasDerivAt_neg_half_sq x).exp).const_mul hoC
  refine (show hoPsi = fun t : ℝ => hoC * Real.exp (-t ^ 2 / 2) from rfl) ▸ h.congr_deriv ?_
  simp only [hoDPsi]
  ring

theorem hasDerivAt_hoDPsi (x : ℝ) : HasDerivAt hoDPsi (hoDDPsi x) x := by
  have hmul : HasDerivAt (fun t : ℝ => hoC * t) hoC x := by
    simpa using (hasDerivAt_id x).const_mul hoC
  have h := (hmul.mul ((hasDerivAt_neg_half_sq x).exp)).neg
  refine (show hoDPsi = fun t : ℝ => -(hoC * t * Real.exp (-t ^ 2 / 2)) from rfl) ▸
    h.congr_deriv ?_
  simp only [hoDDPsi]
  ring

theorem hasDerivAt_hoV (x : ℝ) : HasDerivAt hoV (hoDV x) x := by
  have h := ((hasDerivAt_id x).pow 2).div_const 2
  refine (show hoV = fun t : ℝ => t ^ 2 / 2 from rfl) ▸ h.congr_deriv ?_
  simp [hoDV]

theorem ho_schrodinger (x : ℝ) :
    -(1 / 2) * hoDDPsi x + hoV x * hoPsi x = (1 / 2) * hoPsi x := by
  simp only [hoDDPsi, hoV, hoPsi]
  ring

theorem ho_norm : ∫ x : ℝ, (hoPsi x) ^ 2 = 1 := by
  have hgauss : ∫ x : ℝ, Real.exp (-1 * x ^ 2) = Real.sqrt (Real.pi / 1) := integral_gaussian 1
  have hfun : (fun x : ℝ => (hoPsi x) ^ 2) = fun x : ℝ => hoC ^ 2 * Real.exp (-1 * x ^ 2) := by
    funext x
    rw [hoPsi, mul_pow, exp_neg_half_sq_sq]
    ring_nf
  rw [hfun, integral_const_mul, hgauss, hoC_sq]
  rw [div_one]
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp

/-- Integrability of `c • xⁿ exp (-x²)` written in whatever algebraic shape is needed. -/
theorem integrable_of_eq_pow_mul_gaussian {f : ℝ → ℝ} (c : ℝ) (n : ℕ)
    (hf : ∀ x : ℝ, f x = c * (x ^ n * Real.exp (-x ^ 2))) : Integrable f volume := by
  have := (integrable_pow_mul_gaussian n).const_mul c
  exact this.congr (Filter.Eventually.of_forall fun x => (hf x).symm)

theorem tendsto_of_eq_pow_mul_gaussian_atTop {f : ℝ → ℝ} (c : ℝ) (n : ℕ)
    (hf : ∀ x : ℝ, f x = c * (x ^ n * Real.exp (-x ^ 2))) : Tendsto f atTop (𝓝 0) := by
  have := (tendsto_pow_mul_gaussian_atTop n).const_mul c
  rw [mul_zero] at this
  exact this.congr fun x => (hf x).symm

theorem tendsto_of_eq_pow_mul_gaussian_atBot {f : ℝ → ℝ} (c : ℝ) (n : ℕ)
    (hf : ∀ x : ℝ, f x = c * (x ^ n * Real.exp (-x ^ 2))) : Tendsto f atBot (𝓝 0) := by
  have := (tendsto_pow_mul_gaussian_atBot n).const_mul c
  rw [mul_zero] at this
  exact this.congr fun x => (hf x).symm

/-- **Virial theorem for the harmonic-oscillator ground state.**  All hypotheses of
`Phys.virial_theorem` are verified for `ψ(x) = π^(-1/4) exp(-x²/2)`, `V(x) = x²/2`,
`E = 1/2`; in particular the hypotheses of the general theorem are consistent. -/
theorem harmonic_oscillator_virial :
    2 * (∫ x : ℝ, (1 / 2) * (hoDPsi x) ^ 2) = ∫ x : ℝ, x * hoDV x * (hoPsi x) ^ 2 ∧
      (∫ x : ℝ, ((1 / 2) * (hoDPsi x) ^ 2 + hoV x * (hoPsi x) ^ 2)) = 1 / 2 := by
  refine virial_theorem hoPsi hoDPsi hoDDPsi hoV hoDV (1 / 2)
    hasDerivAt_hoPsi hasDerivAt_hoDPsi hasDerivAt_hoV ho_schrodinger ho_norm
    (integrable_of_eq_pow_mul_gaussian (hoC ^ 2) 0 ?_)
    (integrable_of_eq_pow_mul_gaussian (hoC ^ 2) 2 ?_)
    (integrable_of_eq_pow_mul_gaussian (hoC ^ 2 / 2) 2 ?_)
    (integrable_of_eq_pow_mul_gaussian (hoC ^ 2) 2 ?_)
    (integrable_of_eq_pow_mul_gaussian (-(hoC ^ 2)) 2 ?_)
    (integrable_of_eq_pow_mul_gaussian (-(hoC ^ 2) / 2) 4 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atBot (hoC ^ 2) 1 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atTop (hoC ^ 2) 1 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atBot (hoC ^ 2) 3 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atTop (hoC ^ 2) 3 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atBot (hoC ^ 2 / 2) 3 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atTop (hoC ^ 2 / 2) 3 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atBot (-(hoC ^ 2)) 1 ?_)
    (tendsto_of_eq_pow_mul_gaussian_atTop (-(hoC ^ 2)) 1 ?_) <;>
  · intro x
    have hE : Real.exp (-x ^ 2) = Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) := by
      rw [← Real.exp_add]
      ring_nf
    simp only [hoPsi, hoDPsi, hoV, hoDV, hE]
    ring

end Phys

/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open MeasureTheory Filter Topology

/-- Fundamental theorem of calculus on the whole line, in the form used for
integrating by parts against a decaying boundary term: if `f` is everywhere
differentiable with integrable derivative `f'` and `f → 0` at both ends of the
line, then `∫ f' = 0`. -/
theorem integral_deriv_eq_zero_of_tendsto_zero {f f' : ℝ → ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : Integrable f' volume)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0)) :
    ∫ x : ℝ, f' x = 0 := by
  simpa using MeasureTheory.integral_of_hasDerivAt_of_tendsto hf hf' hbot htop

/-- **Quantum virial theorem** (one dimension, units `ħ = m = 1`).

Let `ψ` be a stationary state of the Schrödinger operator `H = -(1/2) d²/dx² + V`
with energy `E`, i.e. `-(1/2) ψ'' + V ψ = E ψ`, where `dψ`, `ddψ` are the first and
second derivatives of `ψ` and `dV` is the derivative of the potential.  Assume the
state is *bound*: it is normalized, the relevant expectation values converge
(integrability hypotheses), and the boundary terms `x ψ²`, `x (ψ')²`, `x V ψ²`,
`ψ ψ'` all vanish at `±∞`.

Then the virial theorem holds:
`2⟨T⟩ = ⟨x ∂ₓV⟩`, i.e. `2 ∫ (1/2)(ψ')² = ∫ x V'(x) ψ(x)²`,
and moreover the energy is the expectation value of the Hamiltonian,
`⟨T⟩ + ⟨V⟩ = E`. -/
theorem virial_theorem
    (ψ dψ ddψ V dV : ℝ → ℝ) (E : ℝ)
    -- `dψ`, `ddψ` are the derivatives of `ψ`, and `dV` the derivative of `V`
    (hψ : ∀ x : ℝ, HasDerivAt ψ (dψ x) x)
    (hdψ : ∀ x : ℝ, HasDerivAt dψ (ddψ x) x)
    (hV : ∀ x : ℝ, HasDerivAt V (dV x) x)
    -- time-independent Schrödinger equation
    (schrodinger : ∀ x : ℝ, -(1 / 2) * ddψ x + V x * ψ x = E * ψ x)
    -- normalization of the bound state
    (hnorm : ∫ x : ℝ, (ψ x) ^ 2 = 1)
    -- the expectation values involved all converge
    (hiN : Integrable (fun x : ℝ => (ψ x) ^ 2) volume)
    (hiP : Integrable (fun x : ℝ => (dψ x) ^ 2) volume)
    (hiS : Integrable (fun x : ℝ => V x * (ψ x) ^ 2) volume)
    (hiU : Integrable (fun x : ℝ => x * dV x * (ψ x) ^ 2) volume)
    (hiR : Integrable (fun x : ℝ => x * ψ x * dψ x) volume)
    (hiQ : Integrable (fun x : ℝ => x * V x * ψ x * dψ x) volume)
    -- the state is bound: all boundary terms decay at infinity
    (hbN : Tendsto (fun x : ℝ => x * (ψ x) ^ 2) atBot (𝓝 0))
    (htN : Tendsto (fun x : ℝ => x * (ψ x) ^ 2) atTop (𝓝 0))
    (hbP : Tendsto (fun x : ℝ => x * (dψ x) ^ 2) atBot (𝓝 0))
    (htP : Tendsto (fun x : ℝ => x * (dψ x) ^ 2) atTop (𝓝 0))
    (hbS : Tendsto (fun x : ℝ => x * V x * (ψ x) ^ 2) atBot (𝓝 0))
    (htS : Tendsto (fun x : ℝ => x * V x * (ψ x) ^ 2) atTop (𝓝 0))
    (hbD : Tendsto (fun x : ℝ => ψ x * dψ x) atBot (𝓝 0))
    (htD : Tendsto (fun x : ℝ => ψ x * dψ x) atTop (𝓝 0)) :
    2 * (∫ x : ℝ, (1 / 2) * (dψ x) ^ 2) = ∫ x : ℝ, x * dV x * (ψ x) ^ 2 ∧
      (∫ x : ℝ, ((1 / 2) * (dψ x) ^ 2 + V x * (ψ x) ^ 2)) = E := by
  -- The Schrödinger equation, solved for the second derivative.
  have key : ∀ x : ℝ, ddψ x = 2 * (V x - E) * ψ x := by
    intro x
    linear_combination (-2 : ℝ) * schrodinger x
  -- Boundary identity A: from `d/dx (x (ψ')²)`.
  have hA : ∀ x : ℝ, HasDerivAt (fun t : ℝ => t * (dψ t) ^ 2)
      ((dψ x) ^ 2 + 4 * (x * V x * ψ x * dψ x) - (4 * E) * (x * ψ x * dψ x)) x := by
    intro x
    have h := (hasDerivAt_id x).mul ((hdψ x).pow 2)
    have hk := key x
    simp only [Pi.pow_apply, id_eq] at h
    convert h using 1
    rw [hk]; ring
  -- Boundary identity B: from `d/dx (x V ψ²)`.
  have hB : ∀ x : ℝ, HasDerivAt (fun t : ℝ => t * V t * (ψ t) ^ 2)
      (V x * (ψ x) ^ 2 + x * dV x * (ψ x) ^ 2 + 2 * (x * V x * ψ x * dψ x)) x := by
    intro x
    have h := ((hasDerivAt_id x).mul (hV x)).mul ((hψ x).pow 2)
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq] at h
    convert h using 1
    ring
  -- Boundary identity C: from `d/dx (x ψ²)`.
  have hC : ∀ x : ℝ, HasDerivAt (fun t : ℝ => t * (ψ t) ^ 2)
      ((ψ x) ^ 2 + 2 * (x * ψ x * dψ x)) x := by
    intro x
    have h := (hasDerivAt_id x).mul ((hψ x).pow 2)
    simp only [Pi.pow_apply, id_eq] at h
    convert h using 1
    ring
  -- Boundary identity D: from `d/dx (ψ ψ')`.
  have hD : ∀ x : ℝ, HasDerivAt (fun t : ℝ => ψ t * dψ t)
      ((dψ x) ^ 2 + 2 * (V x * (ψ x) ^ 2) - (2 * E) * (ψ x) ^ 2) x := by
    intro x
    have h := (hψ x).mul (hdψ x)
    have hk := key x
    convert h using 1
    rw [hk]; ring
  -- Integrability of the individual total derivatives.
  have hiQ4 : Integrable (fun x : ℝ => 4 * (x * V x * ψ x * dψ x)) volume := hiQ.const_mul 4
  have hiQ2 : Integrable (fun x : ℝ => 2 * (x * V x * ψ x * dψ x)) volume := hiQ.const_mul 2
  have hiR4 : Integrable (fun x : ℝ => (4 * E) * (x * ψ x * dψ x)) volume :=
    hiR.const_mul (4 * E)
  have hiR2 : Integrable (fun x : ℝ => 2 * (x * ψ x * dψ x)) volume := hiR.const_mul 2
  have hiS2 : Integrable (fun x : ℝ => 2 * (V x * (ψ x) ^ 2)) volume := hiS.const_mul 2
  have hiN2 : Integrable (fun x : ℝ => (2 * E) * (ψ x) ^ 2) volume := hiN.const_mul (2 * E)
  have hIA : Integrable (fun x : ℝ => (dψ x) ^ 2 + 4 * (x * V x * ψ x * dψ x)) volume :=
    hiP.add hiQ4
  have hIB : Integrable (fun x : ℝ => V x * (ψ x) ^ 2 + x * dV x * (ψ x) ^ 2) volume :=
    hiS.add hiU
  have hID : Integrable (fun x : ℝ => (dψ x) ^ 2 + 2 * (V x * (ψ x) ^ 2)) volume :=
    hiP.add hiS2
  -- Integrate each total derivative over the line; boundary terms vanish.
  have eA := integral_deriv_eq_zero_of_tendsto_zero hA (hIA.sub hiR4) hbP htP
  have eB := integral_deriv_eq_zero_of_tendsto_zero hB (hIB.add hiQ2) hbS htS
  have eC := integral_deriv_eq_zero_of_tendsto_zero hC (hiN.add hiR2) hbN htN
  have eD := integral_deriv_eq_zero_of_tendsto_zero hD (hID.sub hiN2) hbD htD
  -- Split the integrals into the individual expectation values.
  rw [integral_sub hIA hiR4, integral_add hiP hiQ4, integral_const_mul,
    integral_const_mul] at eA
  rw [integral_add hIB hiQ2, integral_add hiS hiU, integral_const_mul] at eB
  rw [integral_add hiN hiR2, integral_const_mul] at eC
  rw [integral_sub hID hiN2, integral_add hiP hiS2, integral_const_mul,
    integral_const_mul] at eD
  have hiPh : Integrable (fun x : ℝ => (1 / 2) * (dψ x) ^ 2) volume := hiP.const_mul (1 / 2)
  refine ⟨?_, ?_⟩
  · rw [integral_const_mul]
    linear_combination (1 / 2 : ℝ) * eA + E * eC - eB + (1 / 2 : ℝ) * eD
  · rw [integral_add hiPh hiS, integral_const_mul]
    linear_combination (1 / 2 : ℝ) * eD + E * hnorm

end Phys

