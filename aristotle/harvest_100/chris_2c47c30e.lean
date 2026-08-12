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

set_option grind.warning false

/-!
# TKNN: the integer quantum Hall conductance is a Chern number times `e² / h`

This file formalises the Thouless–Kohmoto–Nightingale–den Nijs (TKNN) statement in the
standard Bloch-bundle setting, in the gauge-invariant *spectral projector* formulation.

## Setting

A two-dimensional Bloch Hamiltonian gives, for each quasi-momentum `k = (k₁, k₂)` in the
Brillouin torus `[0, 2π]²`, the spectral projector `P k` onto the occupied bands.  Here `P`
is a matrix-valued function on the Brillouin zone,
`P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ`, which for a physical band structure satisfies
`(P k)ᴴ = P k` and `P k * P k = P k`.

* `Frontier.momDeriv₁`, `Frontier.momDeriv₂` are the entrywise partial derivatives of `P`
  with respect to `k₁` and `k₂`.
* `Frontier.berryCurvature P k = i · tr (P k · [∂₁P k, ∂₂P k])` is the (non-abelian) Berry
  curvature of the occupied bundle; it is a real number (`berryCurvature_isReal`).
* `Frontier.chernNumber P = (1 / 2π) ∫_{[0,2π]²} berryCurvature P` is the first Chern number
  of the occupied Bloch bundle.
* `Frontier.hallConductance e ħ P = (e² / ħ) · (2π)⁻² ∫_{[0,2π]²} berryCurvature P` is the
  Kubo linear-response formula for the transverse (Hall) conductance of the filled bands.
* `Frontier.planckOfReduced ħ = 2π ħ` is Planck's constant `h` in terms of `ħ`.

## Main results

* `Frontier.tknn_chern_hall` : `hallConductance e ħ P = chernNumber P * (e² / h)`, i.e. the
  Hall conductance equals the Chern number times the conductance quantum `e²/h`.
* `Frontier.tknn_chern_hall_integer` : the quantised form — if the Chern number is the
  integer `C`, then the Hall conductance is `C · e²/h`.
* `Frontier.berryCurvature_isReal` : the Berry curvature is real.
* `Frontier.berryCurvature_interband` : only interband matrix elements contribute,
  `Ω = i tr (P ∂₁P (1-P) ∂₂P - P ∂₂P (1-P) ∂₁P)` — the Kubo linear-response integrand.
* Base cases: for a band projector that is constant along one momentum direction (in
  particular for a `k`-independent one) the Berry curvature, the Chern number and the Hall
  conductance all vanish.

The topological quantisation itself — that `chernNumber P` is an integer for a smooth family
of projectors over the Brillouin torus — is *not* proved here; it enters
`tknn_chern_hall_integer` as the hypothesis `chernNumber P = C`.
-/

namespace Frontier

open Matrix

variable {n : ℕ}

/-- Planck's constant `h = 2π ħ` expressed through the reduced Planck constant `ħ`. -/
noncomputable def planckOfReduced (hbar : ℝ) : ℝ := 2 * π * hbar

/-- Entrywise partial derivative of a matrix-valued function on the Brillouin zone with
respect to the first quasi-momentum component. -/
noncomputable def momDeriv₁ (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => deriv (fun t : ℝ => P (t, k.2) i j) k.1

/-- Entrywise partial derivative of a matrix-valued function on the Brillouin zone with
respect to the second quasi-momentum component. -/
noncomputable def momDeriv₂ (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => deriv (fun t : ℝ => P (k.1, t) i j) k.2

/-- The Berry curvature of the occupied bands, in the gauge-invariant projector form
`Ω(k) = i · tr (P [∂₁P, ∂₂P])`. -/
noncomputable def berryCurvature (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ) : ℂ :=
  Complex.I * Matrix.trace
    (P k * (momDeriv₁ P k * momDeriv₂ P k - momDeriv₂ P k * momDeriv₁ P k))

/-- The first Chern number of the occupied Bloch bundle: the integral of the Berry curvature
over the Brillouin torus, divided by `2π`. -/
noncomputable def chernNumber (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (1 / (2 * π)) * ∫ k₁ in (0:ℝ)..(2 * π), ∫ k₂ in (0:ℝ)..(2 * π), berryCurvature P (k₁, k₂)

/-- The Kubo (linear response) transverse conductance of the filled bands:
`σ_xy = (e²/ħ) ∫ d²k/(2π)² Ω(k)`. -/
noncomputable def hallConductance (e hbar : ℝ) (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((e : ℂ) ^ 2 / (hbar : ℂ)) * (1 / (2 * π) ^ 2) *
    ∫ k₁ in (0:ℝ)..(2 * π), ∫ k₂ in (0:ℝ)..(2 * π), berryCurvature P (k₁, k₂)

/-! ### Reality of the Berry curvature -/

/-- For Hermitian `P`, `A`, `B`, the trace `tr (P [A, B])` is purely imaginary. -/
theorem trace_hermitian_commutator_conj (P A B : Matrix (Fin n) (Fin n) ℂ)
    (hP : Pᴴ = P) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (starRingEnd ℂ) (Matrix.trace (P * (A * B - B * A)))
      = -Matrix.trace (P * (A * B - B * A)) := by
  have hconj : (P * (A * B - B * A))ᴴ = (B * A - A * B) * P := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hP, hA, hB]
  have h1 : (starRingEnd ℂ) (Matrix.trace (P * (A * B - B * A)))
      = Matrix.trace ((B * A - A * B) * P) := by
    rw [← hconj, Matrix.trace_conjTranspose]
    rfl
  rw [h1, Matrix.trace_mul_comm]
  rw [show P * (A * B - B * A) = -(P * (B * A - A * B)) by noncomm_ring]
  rw [Matrix.trace_neg, neg_neg]

/-- The Berry curvature is real-valued whenever the projector and its momentum derivatives
are Hermitian. -/
theorem berryCurvature_isReal (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ)
    (hP : (P k)ᴴ = P k) (h1 : (momDeriv₁ P k)ᴴ = momDeriv₁ P k)
    (h2 : (momDeriv₂ P k)ᴴ = momDeriv₂ P k) :
    (starRingEnd ℂ) (berryCurvature P k) = berryCurvature P k := by
  have h := trace_hermitian_commutator_conj (P k) (momDeriv₁ P k) (momDeriv₂ P k) hP h1 h2
  simp only [berryCurvature, map_mul, Complex.conj_I, h]
  ring

/-- The derivative of a conjugated path of complex numbers is the conjugate of the
derivative. -/
theorem deriv_conj_eq (f : ℝ → ℂ) (x : ℝ) (hf : DifferentiableAt ℝ f x) :
    deriv (fun t => (starRingEnd ℂ) (f t)) x = (starRingEnd ℂ) (deriv f x) := by
  have := (Complex.conjCLE.hasFDerivAt (x := f x)).comp_hasDerivAt x hf.hasDerivAt
  simpa [Complex.conjCLE] using this.deriv

/-- The first momentum derivative of a Hermitian family of matrices is Hermitian. -/
theorem momDeriv₁_hermitian (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ)
    (hP : ∀ k, (P k)ᴴ = P k)
    (hdiff : ∀ i j, DifferentiableAt ℝ (fun t : ℝ => P (t, k.2) i j) k.1) :
    (momDeriv₁ P k)ᴴ = momDeriv₁ P k := by
  ext i j
  have hentry : ∀ t : ℝ, P (t, k.2) j i = (starRingEnd ℂ) (P (t, k.2) i j) := by
    intro t
    have := congrArg (fun M => M j i) (hP (t, k.2))
    simpa [Matrix.conjTranspose_apply] using this.symm
  simp only [Matrix.conjTranspose_apply, momDeriv₁, Matrix.of_apply]
  rw [show (fun t : ℝ => P (t, k.2) j i) = fun t : ℝ => (starRingEnd ℂ) (P (t, k.2) i j) from
    funext hentry, deriv_conj_eq _ _ (hdiff i j)]
  simp

/-- The second momentum derivative of a Hermitian family of matrices is Hermitian. -/
theorem momDeriv₂_hermitian (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ)
    (hP : ∀ k, (P k)ᴴ = P k)
    (hdiff : ∀ i j, DifferentiableAt ℝ (fun t : ℝ => P (k.1, t) i j) k.2) :
    (momDeriv₂ P k)ᴴ = momDeriv₂ P k := by
  ext i j
  have hentry : ∀ t : ℝ, P (k.1, t) j i = (starRingEnd ℂ) (P (k.1, t) i j) := by
    intro t
    have := congrArg (fun M => M j i) (hP (k.1, t))
    simpa [Matrix.conjTranspose_apply] using this.symm
  simp only [Matrix.conjTranspose_apply, momDeriv₂, Matrix.of_apply]
  rw [show (fun t : ℝ => P (k.1, t) j i) = fun t : ℝ => (starRingEnd ℂ) (P (k.1, t) i j) from
    funext hentry, deriv_conj_eq _ _ (hdiff i j)]
  simp

/-! ### Interband form of the Berry curvature

Only interband (occupied ↔ empty) matrix elements contribute to the Berry curvature; this is
the algebraic content behind the Kubo formula for the Hall conductance. -/

/-- If `P` is idempotent and `A` satisfies the differentiated idempotency relation
`A = P A + A P`, then `P A P = 0`: `A` has no purely intraband part. -/
theorem sandwich_eq_zero (P A : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P)
    (hA : A = P * A + A * P) : P * A * P = 0 := by
  have h : P * A * P = P * A * P + P * A * P := by
    conv_lhs => rw [hA]
    rw [mul_add, add_mul, ← mul_assoc, hP, ← mul_assoc P A P, mul_assoc (P * A) P P, hP]
  have h' : P * A * P + 0 = P * A * P + P * A * P := by simpa using h
  exact (add_left_cancel h').symm

/-- Algebraic interband decomposition: for an idempotent `P` and derivatives `A`, `B`
satisfying the differentiated idempotency relations, the commutator term of the Berry
curvature only involves interband matrix elements `P · (1 - P)`. -/
theorem proj_commutator_interband (P A B : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P)
    (hA : A = P * A + A * P) (hB : B = P * B + B * P) :
    P * (A * B - B * A) = P * A * (1 - P) * B - P * B * (1 - P) * A := by
  have hAz := sandwich_eq_zero P A hP hA
  have hBz := sandwich_eq_zero P B hP hB
  have e1 : P * A * (1 - P) * B = P * A * B := by
    rw [mul_sub, mul_one, sub_mul, hAz, zero_mul, sub_zero, mul_assoc]
  have e2 : P * B * (1 - P) * A = P * B * A := by
    rw [mul_sub, mul_one, sub_mul, hBz, zero_mul, sub_zero, mul_assoc]
  rw [e1, e2, mul_sub, mul_assoc, mul_assoc]

/-- Differentiating `P² = P` in the first momentum direction. -/
theorem momDeriv₁_idem (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ)
    (hidem : ∀ k, P k * P k = P k)
    (hdiff : ∀ i j, DifferentiableAt ℝ (fun t : ℝ => P (t, k.2) i j) k.1) :
    momDeriv₁ P k = P k * momDeriv₁ P k + momDeriv₁ P k * P k := by
  ext i j
  have hfun : (fun t : ℝ => P (t, k.2) i j)
      = fun t : ℝ => ∑ l, P (t, k.2) i l * P (t, k.2) l j := by
    funext t
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) (hidem (t, k.2))
    simpa [Matrix.mul_apply] using this.symm
  have hderiv : HasDerivAt (fun t : ℝ => ∑ l, P (t, k.2) i l * P (t, k.2) l j)
      (∑ l, (deriv (fun t : ℝ => P (t, k.2) i l) k.1 * P k l j
              + P k i l * deriv (fun t : ℝ => P (t, k.2) l j) k.1)) k.1 := by
    refine HasDerivAt.fun_sum fun l _ => ?_
    exact (hdiff i l).hasDerivAt.fun_mul (hdiff l j).hasDerivAt
  have hd : deriv (fun t : ℝ => P (t, k.2) i j) k.1
      = ∑ l, (deriv (fun t : ℝ => P (t, k.2) i l) k.1 * P k l j
              + P k i l * deriv (fun t : ℝ => P (t, k.2) l j) k.1) := by
    rw [hfun]; exact hderiv.deriv
  simp only [momDeriv₁, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [hd, Finset.sum_add_distrib, add_comm]

/-- Differentiating `P² = P` in the second momentum direction. -/
theorem momDeriv₂_idem (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ)
    (hidem : ∀ k, P k * P k = P k)
    (hdiff : ∀ i j, DifferentiableAt ℝ (fun t : ℝ => P (k.1, t) i j) k.2) :
    momDeriv₂ P k = P k * momDeriv₂ P k + momDeriv₂ P k * P k := by
  ext i j
  have hfun : (fun t : ℝ => P (k.1, t) i j)
      = fun t : ℝ => ∑ l, P (k.1, t) i l * P (k.1, t) l j := by
    funext t
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) (hidem (k.1, t))
    simpa [Matrix.mul_apply] using this.symm
  have hderiv : HasDerivAt (fun t : ℝ => ∑ l, P (k.1, t) i l * P (k.1, t) l j)
      (∑ l, (deriv (fun t : ℝ => P (k.1, t) i l) k.2 * P k l j
              + P k i l * deriv (fun t : ℝ => P (k.1, t) l j) k.2)) k.2 := by
    refine HasDerivAt.fun_sum fun l _ => ?_
    exact (hdiff i l).hasDerivAt.fun_mul (hdiff l j).hasDerivAt
  have hd : deriv (fun t : ℝ => P (k.1, t) i j) k.2
      = ∑ l, (deriv (fun t : ℝ => P (k.1, t) i l) k.2 * P k l j
              + P k i l * deriv (fun t : ℝ => P (k.1, t) l j) k.2) := by
    rw [hfun]; exact hderiv.deriv
  simp only [momDeriv₂, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [hd, Finset.sum_add_distrib, add_comm]

/-- **Interband (Kubo) form of the Berry curvature.**  For a differentiable family of band
projectors, the Berry curvature is given purely by interband matrix elements,
`Ω = i tr (P ∂₁P (1-P) ∂₂P - P ∂₂P (1-P) ∂₁P)`, which is the Kubo linear-response
integrand. -/
theorem berryCurvature_interband (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ)
    (hidem : ∀ k, P k * P k = P k)
    (hdiff₁ : ∀ i j, DifferentiableAt ℝ (fun t : ℝ => P (t, k.2) i j) k.1)
    (hdiff₂ : ∀ i j, DifferentiableAt ℝ (fun t : ℝ => P (k.1, t) i j) k.2) :
    berryCurvature P k = Complex.I * Matrix.trace
      (P k * momDeriv₁ P k * (1 - P k) * momDeriv₂ P k
        - P k * momDeriv₂ P k * (1 - P k) * momDeriv₁ P k) := by
  rw [berryCurvature, proj_commutator_interband (P k) (momDeriv₁ P k) (momDeriv₂ P k)
    (hidem k) (momDeriv₁_idem P k hidem hdiff₁) (momDeriv₂_idem P k hidem hdiff₂)]

/-! ### The TKNN formula -/

/-- **TKNN theorem** (integer quantum Hall effect).  The Kubo transverse conductance of a
filled band structure equals the first Chern number of the occupied Bloch bundle times the
conductance quantum `e² / h`, where `h = 2π ħ`. -/
theorem tknn_chern_hall (e hbar : ℝ) (hhbar : hbar ≠ 0)
    (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) :
    hallConductance e hbar P
      = chernNumber P * ((e : ℂ) ^ 2 / (planckOfReduced hbar : ℂ)) := by
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hb : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar
  simp only [hallConductance, chernNumber, planckOfReduced, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp

/-- **Quantisation of the Hall conductance.**  If the Chern number of the occupied bundle is
the integer `C`, the Hall conductance is exactly `C · e² / h`. -/
theorem tknn_chern_hall_integer (e hbar : ℝ) (hhbar : hbar ≠ 0)
    (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (C : ℤ) (hC : chernNumber P = (C : ℂ)) :
    hallConductance e hbar P = (C : ℂ) * ((e : ℂ) ^ 2 / (planckOfReduced hbar : ℂ)) := by
  rw [tknn_chern_hall e hbar hhbar P, hC]

/-! ### Base cases -/

/-- If the band projector does not depend on the second quasi-momentum, the Berry curvature
vanishes identically. -/
theorem berryCurvature_of_indep_k₂ (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ a b b', P (a, b) = P (a, b')) (k : ℝ × ℝ) :
    berryCurvature P k = 0 := by
  have h2 : momDeriv₂ P k = 0 := by
    ext i j
    have : (fun t : ℝ => P (k.1, t) i j) = fun _ : ℝ => P (k.1, k.2) i j := by
      funext t
      rw [hP k.1 t k.2]
    simp [momDeriv₂, this]
  simp [berryCurvature, h2]

/-- If the band projector does not depend on the second quasi-momentum, its Chern number
vanishes. -/
theorem chernNumber_of_indep_k₂ (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ a b b', P (a, b) = P (a, b')) : chernNumber P = 0 := by
  simp [chernNumber, berryCurvature_of_indep_k₂ P hP]

/-- Base case of TKNN: a band structure that is constant along one momentum direction is
topologically trivial and carries no Hall current. -/
theorem hallConductance_of_indep_k₂ (e hbar : ℝ) (hhbar : hbar ≠ 0)
    (P : ℝ × ℝ → Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b b', P (a, b) = P (a, b')) :
    hallConductance e hbar P = 0 := by
  rw [tknn_chern_hall e hbar hhbar, chernNumber_of_indep_k₂ P hP, zero_mul]

/-! ### Base case: a momentum-independent band projector -/

/-- A `k`-independent band projector has vanishing Berry curvature. -/
theorem berryCurvature_const (Q : Matrix (Fin n) (Fin n) ℂ) (k : ℝ × ℝ) :
    berryCurvature (fun _ => Q) k = 0 := by
  exact berryCurvature_of_indep_k₂ _ (fun _ _ _ => rfl) k

/-- A `k`-independent band projector describes a topologically trivial band: its Chern
number vanishes. -/
theorem chernNumber_const (Q : Matrix (Fin n) (Fin n) ℂ) :
    chernNumber (fun _ => Q) = 0 := by
  simp [chernNumber, berryCurvature_const Q]

/-- Base case of TKNN: a trivial (momentum-independent) band structure carries no Hall
current, consistent with Chern number `0`. -/
theorem hallConductance_const (e hbar : ℝ) (hhbar : hbar ≠ 0)
    (Q : Matrix (Fin n) (Fin n) ℂ) :
    hallConductance e hbar (fun _ => Q) = 0 := by
  rw [tknn_chern_hall e hbar hhbar, chernNumber_const, zero_mul]

end Frontier

