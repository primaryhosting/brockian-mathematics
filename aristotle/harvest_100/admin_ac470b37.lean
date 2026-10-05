import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Phys

open Complex MeasureTheory Filter Topology

/-- The expectation value `⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/
noncomputable def expectation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) (psi : E) : ℂ :=
  inner ℂ psi (A psi)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An eigenvalue of a symmetric operator, on a nonzero eigenvector, is real. -/
theorem eigenvalue_isReal (H : E →ₗ[ℂ] E) (psi : E) (E₀ : ℂ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (hpsi : psi ≠ 0) (heig : H psi = E₀ • psi) :
    (starRingEnd ℂ) E₀ = E₀ := by
  have h1 := hsymm psi psi
  rw [heig, inner_smul_left, inner_smul_right] at h1
  have h2 : (inner ℂ psi psi : ℂ) ≠ 0 := by simpa using hpsi
  exact mul_right_cancel₀ h2 h1

/-- For a stationary state (an eigenvector of a symmetric Hamiltonian), the expectation
value of any commutator `[H, A]` vanishes. -/
theorem expectation_commutator_eq_zero (H A : E →ₗ[ℂ] E) (psi : E) (E₀ : ℂ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (hpsi : psi ≠ 0) (heig : H psi = E₀ • psi) :
    inner ℂ psi (H (A psi) - A (H psi)) = (0 : ℂ) := by
  have hreal : (starRingEnd ℂ) E₀ = E₀ := eigenvalue_isReal H psi E₀ hsymm hpsi heig
  rw [inner_sub_right, ← hsymm psi (A psi), heig, map_smul, inner_smul_left, inner_smul_right,
    hreal, sub_self]

/-- **Quantum virial theorem.**

Let `H` be a (symmetric) Hamiltonian, `psi` a normalized bound stationary state, i.e. a unit
eigenvector of `H`, and let `A` be the generator of dilations `A = r · p`.  The defining
algebraic property of `A` is the commutator identity `[H, A] = i (2 T - W)`, where `T` is the
kinetic energy operator and `W = r · ∇V` the virial operator.  Then
`2 ⟨T⟩ = ⟨r · ∇V⟩`. -/
theorem virial_theorem (H A T W : E →ₗ[ℂ] E) (psi : E) (E₀ : ℂ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (hnorm : ‖psi‖ = 1)
    (heig : H psi = E₀ • psi)
    (hcomm : ∀ x : E, H (A x) - A (H x) = Complex.I • ((2 : ℂ) • T x - W x)) :
    2 * expectation T psi = expectation W psi := by
  have hpsi : psi ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hcomm0 := expectation_commutator_eq_zero H A psi E₀ hsymm hpsi heig
  rw [hcomm psi, inner_smul_right, inner_sub_right, inner_smul_right] at hcomm0
  rcases mul_eq_zero.mp hcomm0 with h | h
  · exact absurd h Complex.I_ne_zero
  · unfold expectation
    linear_combination h

/-- The hypotheses of `virial_theorem` are consistent: for arbitrary `H`, `A`, `T`, the virial
operator `W = 2T + i [H, A]` satisfies the commutator identity `[H, A] = i (2T - W)`. -/
theorem exists_virial_operator (H A T : E →ₗ[ℂ] E) :
    ∀ x : E, H (A x) - A (H x)
      = Complex.I • ((2 : ℂ) • T x
          - ((2 : ℂ) • T + Complex.I • (H ∘ₗ A - A ∘ₗ H)) x) := by
  intro x
  simp [LinearMap.sub_apply, smul_smul, Complex.I_mul_I]

/-! ## A concrete instance: the one-dimensional harmonic oscillator ground state -/

/-- The (normalized) ground state of the one–dimensional harmonic oscillator
`H = -½ d²/dx² + ½ x²`. -/
noncomputable def psiHO (x : ℝ) : ℝ := Real.pi ^ (-(1 : ℝ) / 4) * Real.exp (-x ^ 2 / 2)

/-- The harmonic oscillator potential `V(x) = x²/2`. -/
noncomputable def VHO (x : ℝ) : ℝ := x ^ 2 / 2

theorem integrable_gaussian_kernel : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem integrable_sq_mul_gaussian_kernel :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := 2) (by norm_num)
  simpa [Real.rpow_natCast] using h

theorem integral_gaussian_kernel : ∫ x : ℝ, Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

theorem gaussian_tendsto_atTop : Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun x : ℝ => x⁻¹)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h1 : x ^ 2 ≤ Real.exp (x ^ 2) := by nlinarith [Real.add_one_le_exp (x ^ 2)]
    have he : (0 : ℝ) < Real.exp (x ^ 2) := Real.exp_pos _
    rw [Real.exp_neg, inv_eq_one_div, mul_one_div, div_le_iff₀ he]
    calc x = x⁻¹ * x ^ 2 := by field_simp
      _ ≤ x⁻¹ * Real.exp (x ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
  · exact tendsto_inv_atTop_zero

theorem gaussian_tendsto_atBot : Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := (gaussian_tendsto_atTop.comp tendsto_neg_atBot_atTop).neg
  simpa [Function.comp_def] using h

/-- The second moment of the Gaussian: `∫ x² e^{-x²} dx = √π / 2`. -/
theorem gaussian_second_moment :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  set f : ℝ → ℝ := fun x => -(1 / 2) * (x * Real.exp (-x ^ 2)) with hf
  set f' : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-x ^ 2) - (1 / 2) * Real.exp (-x ^ 2) with hf'
  have hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).neg
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2)) (Real.exp (-x ^ 2) * (-(2 * x))) x :=
      (Real.hasDerivAt_exp _).comp x h1
    have h3 : HasDerivAt (fun x : ℝ => x * Real.exp (-x ^ 2))
        (1 * Real.exp (-x ^ 2) + x * (Real.exp (-x ^ 2) * (-(2 * x)))) x :=
      (hasDerivAt_id x).mul h2
    have h4 := h3.const_mul (-(1 / 2) : ℝ)
    convert h4 using 1
    simp [hf']
    ring
  have hintf' : Integrable f' := by
    simpa [hf'] using
      integrable_sq_mul_gaussian_kernel.sub (integrable_gaussian_kernel.const_mul (1 / 2 : ℝ))
  have hzero : ∫ x : ℝ, f' x = 0 := by
    have := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hintf'
      (by simpa [hf] using gaussian_tendsto_atBot.const_mul (-(1 / 2) : ℝ))
      (by simpa [hf] using gaussian_tendsto_atTop.const_mul (-(1 / 2) : ℝ))
    simpa using this
  have hsplit : ∫ x : ℝ, f' x
      = (∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2)) - (1 / 2) * ∫ x : ℝ, Real.exp (-x ^ 2) := by
    rw [hf', MeasureTheory.integral_sub integrable_sq_mul_gaussian_kernel
      (integrable_gaussian_kernel.const_mul (1 / 2 : ℝ)), MeasureTheory.integral_const_mul]
  rw [hzero, integral_gaussian_kernel] at hsplit
  linarith

theorem psiHO_sq (x : ℝ) : psiHO x ^ 2 = (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [psiHO, mul_pow, ← Real.rpow_natCast (Real.pi ^ (-(1 : ℝ) / 4)) 2, ← Real.rpow_mul hpi.le,
    ← Real.exp_nat_mul]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hpi.le]
  norm_num
  left
  ring

/-- The ground state is normalized: `∫ ψ² = 1`. -/
theorem psiHO_normalized : ∫ x : ℝ, psiHO x ^ 2 = 1 := by
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  simp only [psiHO_sq]
  rw [MeasureTheory.integral_const_mul, integral_gaussian_kernel]
  field_simp

theorem psiHO_hasDerivAt (x : ℝ) : HasDerivAt psiHO (-x * psiHO x) x := by
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-x) x := by
    have h0 := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert h0 using 1
    push_cast
    ring
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (Real.exp (-x ^ 2 / 2) * (-x)) x :=
    (Real.hasDerivAt_exp _).comp x h1
  have h3 := h2.const_mul (Real.pi ^ (-(1 : ℝ) / 4))
  convert h3 using 1
  simp [psiHO]
  ring

theorem psiHO_deriv_eq : deriv psiHO = fun x => -x * psiHO x :=
  funext fun x => (psiHO_hasDerivAt x).deriv

/-- The ground state satisfies the Schrödinger equation `-½ψ'' + ½x²ψ = ½ψ`, since
`ψ'' = (x² - 1) ψ`. -/
theorem psiHO_deriv2 (x : ℝ) : deriv (deriv psiHO) x = (x ^ 2 - 1) * psiHO x := by
  rw [psiHO_deriv_eq]
  have h : HasDerivAt (fun y : ℝ => -y * psiHO y) (-1 * psiHO x + -x * (-x * psiHO x)) x :=
    ((hasDerivAt_id x).neg).mul (psiHO_hasDerivAt x)
  rw [h.deriv]
  ring

theorem VHO_deriv (x : ℝ) : deriv VHO x = x := by
  have h : HasDerivAt VHO x x := by
    have h0 := (hasDerivAt_pow 2 x).div_const 2
    convert h0 using 1
    push_cast
    ring
  exact h.deriv

/-- The expected kinetic energy of the harmonic oscillator ground state is `1/4`. -/
theorem psiHO_kinetic :
    (∫ x : ℝ, psiHO x * (-(1 / 2) * deriv (deriv psiHO) x)) = 1 / 4 := by
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have hfun : (fun x : ℝ => psiHO x * (-(1 / 2) * deriv (deriv psiHO) x))
      = fun x : ℝ => (-(1 / 2) * (Real.sqrt Real.pi)⁻¹) * (x ^ 2 * Real.exp (-x ^ 2))
          + ((1 / 2) * (Real.sqrt Real.pi)⁻¹) * Real.exp (-x ^ 2) := by
    funext x
    rw [psiHO_deriv2]
    have h1 : psiHO x * (-(1 / 2) * ((x ^ 2 - 1) * psiHO x))
        = -(1 / 2) * (x ^ 2 - 1) * psiHO x ^ 2 := by ring
    rw [h1, psiHO_sq]
    ring
  rw [hfun, MeasureTheory.integral_add (integrable_sq_mul_gaussian_kernel.const_mul _)
      (integrable_gaussian_kernel.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_gaussian_kernel, gaussian_second_moment]
  field_simp
  ring

/-- The expected virial `⟨x V'(x)⟩` of the harmonic oscillator ground state is `1/2`. -/
theorem psiHO_virialExpectation :
    (∫ x : ℝ, psiHO x * ((x * deriv VHO x) * psiHO x)) = 1 / 2 := by
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have hfun : (fun x : ℝ => psiHO x * ((x * deriv VHO x) * psiHO x))
      = fun x : ℝ => (Real.sqrt Real.pi)⁻¹ * (x ^ 2 * Real.exp (-x ^ 2)) := by
    funext x
    rw [VHO_deriv]
    have h1 : psiHO x * (x * x * psiHO x) = x ^ 2 * psiHO x ^ 2 := by ring
    rw [h1, psiHO_sq]
    ring
  rw [hfun, MeasureTheory.integral_const_mul, gaussian_second_moment]
  field_simp

/-- **The virial theorem for the harmonic oscillator ground state**: with kinetic energy
`T = -½ d²/dx²` and potential `V(x) = x²/2`, the normalized ground state satisfies
`2⟨T⟩ = ⟨x V'(x)⟩` (both sides equal `1/2`). -/
theorem virial_theorem_harmonicOscillator :
    2 * (∫ x : ℝ, psiHO x * (-(1 / 2) * deriv (deriv psiHO) x))
      = ∫ x : ℝ, psiHO x * ((x * deriv VHO x) * psiHO x) := by
  rw [psiHO_kinetic, psiHO_virialExpectation]
  norm_num

end Phys

