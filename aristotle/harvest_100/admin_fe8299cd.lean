/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped InnerProductSpace

namespace Phys

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Setup

Throughout, `H s` is a time–dependent (self-adjoint) Hamiltonian, `Ev s` a real eigenvalue,
and `P s` the orthogonal projection onto the corresponding eigenspace.  `P₁`, `P₂` are the
first and second derivatives of `P`, `H'` the derivative of `H` and `Ev'` the derivative of `Ev`.
-/

section Defs

variable (H H' P P₁ : ℝ → (E →L[ℂ] E)) (Ev Ev' : ℝ → ℝ)

/-- The shifted Hamiltonian `H s - Ev s` with the eigenprojection added, so that it becomes
invertible exactly when `Ev s` is an isolated (gapped) eigenvalue. -/
def shiftUnit (s : ℝ) : E →L[ℂ] E := H s - ((Ev s : ℂ)) • 1 + P s

/-- Derivative of `shiftUnit`. -/
def shiftUnit' (s : ℝ) : E →L[ℂ] E := H' s - ((Ev' s : ℂ)) • 1 + P₁ s

/-- The reduced resolvent: the inverse of `H s - Ev s` on the range of `1 - P s`, and `0`
on the range of `P s`. -/
def redRes (s : ℝ) : E →L[ℂ] E := Ring.inverse (shiftUnit H P Ev s) - P s

/-- Derivative of the reduced resolvent. -/
def redRes' (s : ℝ) : E →L[ℂ] E :=
  -(Ring.inverse (shiftUnit H P Ev s) * shiftUnit' H' P₁ Ev' s *
      Ring.inverse (shiftUnit H P Ev s)) - P₁ s

end Defs

section Aux

variable (H H' P P₁ P₂ : ℝ → (E →L[ℂ] E)) (Ev Ev' : ℝ → ℝ)

/-- The operator solving the commutator equation `[H s, X s] = P₁ s`. -/
def katoX (s : ℝ) : E →L[ℂ] E :=
  redRes H P Ev s * P₁ s * P s - P s * P₁ s * redRes H P Ev s

/-- Derivative of `katoX`. -/
def katoX' (s : ℝ) : E →L[ℂ] E :=
  (redRes' H H' P P₁ Ev Ev' s * P₁ s * P s + redRes H P Ev s * P₂ s * P s +
      redRes H P Ev s * P₁ s * P₁ s) -
    (P₁ s * P₁ s * redRes H P Ev s + P s * P₂ s * redRes H P Ev s +
      P s * P₁ s * redRes' H H' P P₁ Ev Ev' s)

end Aux

/-! ## Basic algebraic facts -/

variable {H H' P P₁ P₂ : ℝ → (E →L[ℂ] E)} {Ev Ev' : ℝ → ℝ}

/-- The eigenrelation on the left, obtained from the one on the right by taking adjoints. -/
lemma proj_mul_ham (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s) (s : ℝ) :
    P s * H s = ((Ev s : ℂ)) • P s := by
  have h := congrArg star (heig s)
  simpa [star_mul, (hHsa s).star_eq, (hPsa s).star_eq, Complex.conj_ofReal] using h

omit [CompleteSpace E] in
/-- `(H - Ev) P = 0`. -/
lemma sub_mul_proj (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s) (s : ℝ) :
    (H s - ((Ev s : ℂ)) • 1) * P s = 0 := by
  rw [sub_mul, heig s, smul_mul_assoc, one_mul, sub_self]

/-- `P (H - Ev) = 0`. -/
lemma proj_mul_sub (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s) (s : ℝ) :
    P s * (H s - ((Ev s : ℂ)) • 1) = 0 := by
  rw [mul_sub, proj_mul_ham hHsa hPsa heig s, mul_smul_comm, mul_one, sub_self]

omit [CompleteSpace E] in
/-- The shifted operator acts as the identity on the range of `P`. -/
lemma shiftUnit_mul_proj (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s) (s : ℝ) :
    shiftUnit H P Ev s * P s = P s := by
  rw [shiftUnit, add_mul, sub_mul_proj heig s, hPidem s, zero_add]

lemma proj_mul_shiftUnit (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s) (s : ℝ) :
    P s * shiftUnit H P Ev s = P s := by
  rw [shiftUnit, mul_add, proj_mul_sub hHsa hPsa heig s, hPidem s, zero_add]

omit [CompleteSpace E] in
lemma inv_mul_proj (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    Ring.inverse (shiftUnit H P Ev s) * P s = P s := by
  conv_lhs => rw [← shiftUnit_mul_proj hPidem heig s]
  rw [← mul_assoc, Ring.inverse_mul_cancel _ (hgap s), one_mul]

lemma proj_mul_inv (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    P s * Ring.inverse (shiftUnit H P Ev s) = P s := by
  conv_lhs => rw [← proj_mul_shiftUnit hHsa hPsa hPidem heig s]
  rw [mul_assoc, Ring.mul_inverse_cancel _ (hgap s), mul_one]

omit [CompleteSpace E] in
lemma sub_eq_shiftUnit_sub_proj (s : ℝ) :
    H s - ((Ev s : ℂ)) • 1 = shiftUnit H P Ev s - P s := by
  simp [shiftUnit]

/-- `S (H - Ev) = 1 - P`. -/
lemma redRes_mul_sub (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    redRes H P Ev s * (H s - ((Ev s : ℂ)) • 1) = 1 - P s := by
  rw [redRes, sub_mul, proj_mul_sub hHsa hPsa heig s, sub_zero,
    sub_eq_shiftUnit_sub_proj (H := H) (P := P) (Ev := Ev) s, mul_sub,
    Ring.inverse_mul_cancel _ (hgap s), inv_mul_proj hPidem heig hgap s]

/-- `(H - Ev) S = 1 - P`. -/
lemma sub_mul_redRes (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    (H s - ((Ev s : ℂ)) • 1) * redRes H P Ev s = 1 - P s := by
  rw [redRes, mul_sub, sub_mul_proj heig s, sub_zero,
    sub_eq_shiftUnit_sub_proj (H := H) (P := P) (Ev := Ev) s, sub_mul,
    Ring.mul_inverse_cancel _ (hgap s), proj_mul_inv hHsa hPsa hPidem heig hgap s]

omit [CompleteSpace E] in
/-- `S P = 0`. -/
lemma redRes_mul_proj (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    redRes H P Ev s * P s = 0 := by
  rw [redRes, sub_mul, inv_mul_proj hPidem heig hgap s, hPidem s, sub_self]

/-- `P S = 0`. -/
lemma proj_mul_redRes (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    P s * redRes H P Ev s = 0 := by
  rw [redRes, mul_sub, proj_mul_inv hHsa hPsa hPidem heig hgap s, hPidem s, sub_self]

/-- Differentiating `P * P = P`. -/
lemma proj_deriv_decomp (hPidem : ∀ s, P s * P s = P s)
    (hP : ∀ s, HasDerivAt P (P₁ s) s) (s : ℝ) :
    P s * P₁ s + P₁ s * P s = P₁ s := by
  have h1 : HasDerivAt (fun t => P t * P t) (P₁ s * P s + P s * P₁ s) s := (hP s).mul (hP s)
  have hEq : (fun t => P t * P t) = P := funext hPidem
  rw [hEq] at h1
  rw [add_comm]
  exact h1.unique (hP s)

/-- `P P₁ P = 0`. -/
lemma proj_deriv_proj (hPidem : ∀ s, P s * P s = P s)
    (hP : ∀ s, HasDerivAt P (P₁ s) s) (s : ℝ) :
    P s * P₁ s * P s = 0 := by
  have h := proj_deriv_decomp hPidem hP s
  have h2 : P s * (P s * P₁ s + P₁ s * P s) = P s * P₁ s := by rw [h]
  rw [mul_add, ← mul_assoc, hPidem s, ← mul_assoc] at h2
  exact add_left_cancel (h2.trans (add_zero (P s * P₁ s)).symm)

/-- Pure ring-theoretic form of the commutator identity. -/
lemma comm_aux {R : Type*} [Ring R] (D S Pr Q : R)
    (h1 : S * D = 1 - Pr) (h2 : D * S = 1 - Pr) (h3 : D * Pr = 0) (h4 : Pr * D = 0)
    (h5 : Pr * Q + Q * Pr = Q) (h6 : Pr * Q * Pr = 0) :
    D * (S * Q * Pr - Pr * Q * S) - (S * Q * Pr - Pr * Q * S) * D = Q := by
  have e1 : D * (S * Q * Pr - Pr * Q * S) - (S * Q * Pr - Pr * Q * S) * D
      = (D * S) * Q * Pr - (D * Pr) * Q * S - (S * Q * (Pr * D) - Pr * Q * (S * D)) := by
    noncomm_ring
  rw [e1, h1, h2, h3, h4]
  have e2 : (1 - Pr) * Q * Pr - 0 * Q * S - (S * Q * 0 - Pr * Q * (1 - Pr))
      = (Pr * Q + Q * Pr) - (Pr * Q * Pr) - (Pr * Q * Pr) := by noncomm_ring
  rw [e2, h5, h6, sub_zero, sub_zero]

/-- The commutator equation `[H, X] = P₁`. -/
lemma commutator_katoX (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (hPidem : ∀ s, P s * P s = P s)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s))
    (hP : ∀ s, HasDerivAt P (P₁ s) s) (s : ℝ) :
    H s * katoX H P P₁ Ev s - katoX H P P₁ Ev s * H s = P₁ s := by
  have hshift : ∀ Y : E →L[ℂ] E,
      H s * Y - Y * H s = (H s - ((Ev s : ℂ)) • 1) * Y - Y * (H s - ((Ev s : ℂ)) • 1) := by
    intro Y
    rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  rw [katoX, hshift]
  exact comm_aux _ _ _ _ (redRes_mul_sub hHsa hPsa hPidem heig hgap s)
    (sub_mul_redRes hHsa hPsa hPidem heig hgap s) (sub_mul_proj heig s)
    (proj_mul_sub hHsa hPsa heig s) (proj_deriv_decomp hPidem hP s)
    (proj_deriv_proj hPidem hP s)

/-! ## Differentiability -/

lemma hasDerivAt_ringInverse_comp {M M' : ℝ → (E →L[ℂ] E)} {s : ℝ}
    (h : HasDerivAt M (M' s) s) (hu : IsUnit (M s)) :
    HasDerivAt (fun t => Ring.inverse (M t))
      (-(Ring.inverse (M s) * M' s * Ring.inverse (M s))) s := by
  obtain ⟨u, hu⟩ := hu
  have h1 : HasFDerivAt (Ring.inverse (M₀ := (E →L[ℂ] E)))
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℂ] E) (↑u⁻¹) (↑u⁻¹)) (M s) := by
    rw [← hu]; exact hasFDerivAt_ringInverse u
  simpa [← hu, Ring.inverse_unit] using h1.comp_hasDerivAt s h

lemma hasDerivAt_shiftUnit (hH : ∀ s, HasDerivAt H (H' s) s)
    (hEv : ∀ s, HasDerivAt Ev (Ev' s) s) (hP : ∀ s, HasDerivAt P (P₁ s) s) (s : ℝ) :
    HasDerivAt (shiftUnit H P Ev) (shiftUnit' H' P₁ Ev' s) s :=
  ((hH s).sub (((hEv s).ofReal_comp).smul_const _)).add (hP s)

lemma hasDerivAt_redRes (hH : ∀ s, HasDerivAt H (H' s) s)
    (hEv : ∀ s, HasDerivAt Ev (Ev' s) s) (hP : ∀ s, HasDerivAt P (P₁ s) s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    HasDerivAt (redRes H P Ev) (redRes' H H' P P₁ Ev Ev' s) s :=
  (hasDerivAt_ringInverse_comp (M' := shiftUnit' H' P₁ Ev')
    (hasDerivAt_shiftUnit hH hEv hP s) (hgap s)).sub (hP s)

lemma hasDerivAt_katoX (hH : ∀ s, HasDerivAt H (H' s) s)
    (hEv : ∀ s, HasDerivAt Ev (Ev' s) s) (hP : ∀ s, HasDerivAt P (P₁ s) s)
    (hP1 : ∀ s, HasDerivAt P₁ (P₂ s) s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) (s : ℝ) :
    HasDerivAt (katoX H P P₁ Ev) (katoX' H H' P P₁ P₂ Ev Ev' s) s := by
  have hS := hasDerivAt_redRes hH hEv hP hgap s
  have h := ((hS.mul (hP1 s)).mul (hP s)).sub (((hP s).mul (hP1 s)).mul hS)
  convert h using 1

lemma continuous_katoX (hH : ∀ s, HasDerivAt H (H' s) s)
    (hEv : ∀ s, HasDerivAt Ev (Ev' s) s) (hP : ∀ s, HasDerivAt P (P₁ s) s)
    (hP1 : ∀ s, HasDerivAt P₁ (P₂ s) s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) :
    Continuous (katoX H P P₁ Ev) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_katoX hH hEv hP hP1 hgap s).continuousAt

lemma continuous_katoX' (hH : ∀ s, HasDerivAt H (H' s) s) (hH' : Continuous H')
    (hEv : ∀ s, HasDerivAt Ev (Ev' s) s) (hEv' : Continuous Ev')
    (hP : ∀ s, HasDerivAt P (P₁ s) s) (hP1 : ∀ s, HasDerivAt P₁ (P₂ s) s)
    (hP2 : Continuous P₂)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) :
    Continuous (katoX' H H' P P₁ P₂ Ev Ev') := by
  have hcP : Continuous P :=
    continuous_iff_continuousAt.2 fun s => (hP s).continuousAt
  have hcP1 : Continuous P₁ :=
    continuous_iff_continuousAt.2 fun s => (hP1 s).continuousAt
  have hcinv : Continuous (fun t => Ring.inverse (shiftUnit H P Ev t)) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_ringInverse_comp (M' := shiftUnit' H' P₁ Ev')
        (hasDerivAt_shiftUnit hH hEv hP s) (hgap s)).continuousAt
  have hcS : Continuous (redRes H P Ev) := by
    simpa [redRes] using hcinv.sub hcP
  have hcM' : Continuous (shiftUnit' H' P₁ Ev') := by
    have : Continuous (fun t => ((Ev' t : ℂ)) • (1 : E →L[ℂ] E)) :=
      (Complex.continuous_ofReal.comp hEv').smul continuous_const
    simpa [shiftUnit'] using (hH'.sub this).add hcP1
  have hcS' : Continuous (redRes' H H' P P₁ Ev Ev') := by
    simpa [redRes'] using (((hcinv.mul hcM').mul hcinv).neg).sub hcP1
  simpa [katoX'] using
    ((((hcS'.mul hcP1).mul hcP).add ((hcS.mul hP2).mul hcP)).add ((hcS.mul hcP1).mul hcP1)).sub
      ((((hcP1.mul hcP1).mul hcS).add ((hcP.mul hP2).mul hcS)).add ((hcP.mul hcP1).mul hcS'))

/-! ## The Schrödinger evolution -/

/-- Derivative of `t ↦ ⟪ψ t, A t (ψ t)⟫` along a solution of the Schrödinger equation. -/
lemma hasDerivAt_inner_apply (hHsa : ∀ s, IsSelfAdjoint (H s)) {T : ℝ} {ψ : ℝ → E}
    (hψ : ∀ s, HasDerivAt ψ ((-(Complex.I * (T : ℂ))) • (H s) (ψ s)) s)
    {A A' : ℝ → (E →L[ℂ] E)} {s : ℝ} (hA : HasDerivAt A (A' s) s) :
    HasDerivAt (fun t => ⟪ψ t, A t (ψ t)⟫_ℂ)
      (⟪ψ s, A' s (ψ s)⟫_ℂ +
        (Complex.I * (T : ℂ)) * ⟪ψ s, (H s * A s - A s * H s) (ψ s)⟫_ℂ) s := by
  have hAr : HasDerivAt (fun t => (A t).restrictScalars ℝ) ((A' s).restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt s hA
  have h := (hψ s).inner ℂ (hAr.clm_apply (hψ s))
  convert h using 1
  have hst : ContinuousLinearMap.adjoint (H s) = H s := by
    have h2 := (hHsa s).star_eq
    rwa [ContinuousLinearMap.star_eq_adjoint] at h2
  have hsa : ⟪(H s) (ψ s), A s (ψ s)⟫_ℂ = ⟪ψ s, (H s) (A s (ψ s))⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right (H s) (ψ s) (A s (ψ s)), hst]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, inner_sub_right,
    inner_add_right, inner_smul_right, inner_smul_left, map_smul, hsa,
    map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
    ContinuousLinearMap.coe_restrictScalars']
  ring

/-- Conservation of the norm. -/
lemma norm_psi_const (hHsa : ∀ s, IsSelfAdjoint (H s)) {T : ℝ} {ψ : ℝ → E}
    (hψ : ∀ s, HasDerivAt ψ ((-(Complex.I * (T : ℂ))) • (H s) (ψ s)) s) (s : ℝ) :
    ‖ψ s‖ = ‖ψ 0‖ := by
  have hd : ∀ t : ℝ, HasDerivAt (fun r => ⟪ψ r, ψ r⟫_ℂ) 0 t := by
    intro t
    have h := hasDerivAt_inner_apply hHsa hψ (A := fun _ => (1 : E →L[ℂ] E)) (A' := fun _ => 0)
      (s := t) (hasDerivAt_const t _)
    simpa using h
  have h2 := is_const_of_deriv_eq_zero (𝕜 := ℝ) (f := fun r => ⟪ψ r, ψ r⟫_ℂ)
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s 0
  simp only [inner_self_eq_norm_sq_to_K] at h2
  have h3 : (‖ψ s‖ : ℝ) ^ 2 = (‖ψ 0‖ : ℝ) ^ 2 := by exact_mod_cast h2
  nlinarith [norm_nonneg (ψ s), norm_nonneg (ψ 0)]

/-! ## The adiabatic theorem -/

/--
**Adiabatic theorem.**

Let `H : ℝ → (E →L[ℂ] E)` be a `C¹` family of self-adjoint operators on a complex Hilbert
space `E`, let `Ev : ℝ → ℝ` be a `C¹` family of eigenvalues and `P : ℝ → (E →L[ℂ] E)` a `C²`
family of orthogonal projections onto the corresponding eigenspaces (`H s * P s = Ev s • P s`).
Assume the eigenvalue is *nondegenerate* (each `P s` is a rank-one projection onto a unit
vector) and *gapped*, encoded by the invertibility of `H s - Ev s + P s`.

Then there is a constant `C` such that for every adiabatic parameter `T ≥ 1` and every
solution `ψ` of the Schrödinger equation `ψ' = -i T H(s) ψ` starting in the eigenspace at
time `0`, the state stays in the instantaneous eigenspace up to an error `O(1/T)`:
`‖ψ s - P s (ψ s)‖² ≤ C / T` for all `s ∈ [0,1]`.

The nondegeneracy hypothesis `hrank` is stated because it is part of the physical statement;
the proof in fact works for the spectral projection of any isolated eigenvalue.
-/
theorem adiabatic_theorem
    (H H' P P₁ P₂ : ℝ → (E →L[ℂ] E)) (Ev Ev' : ℝ → ℝ)
    (hH : ∀ s, HasDerivAt H (H' s) s) (hH' : Continuous H')
    (hEv : ∀ s, HasDerivAt Ev (Ev' s) s) (hEv' : Continuous Ev')
    (hP : ∀ s, HasDerivAt P (P₁ s) s) (hP1 : ∀ s, HasDerivAt P₁ (P₂ s) s)
    (hP2 : Continuous P₂)
    (hHsa : ∀ s, IsSelfAdjoint (H s)) (hPsa : ∀ s, IsSelfAdjoint (P s))
    (hPidem : ∀ s, P s * P s = P s)
    (hrank : ∀ s, ∃ v : E, ‖v‖ = 1 ∧ ∀ x, P s x = ⟪v, x⟫_ℂ • v)
    (heig : ∀ s, H s * P s = ((Ev s : ℂ)) • P s)
    (hgap : ∀ s, IsUnit (shiftUnit H P Ev s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ ψ : ℝ → E,
      (∀ s, HasDerivAt ψ ((-(Complex.I * (T : ℂ))) • (H s) (ψ s)) s) →
      ‖ψ 0‖ = 1 → P 0 (ψ 0) = ψ 0 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖ψ s - P s (ψ s)‖ ^ 2 ≤ C / T := by
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_katoX hH hEv hP hP1 hgap).continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_katoX' hH hH' hEv hEv' hP hP1 hP2 hgap).continuousOn
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hB0nn : 0 ≤ B0 := le_trans (norm_nonneg _) (hB0 0 hmem0)
  have hB1nn : 0 ≤ B1 := le_trans (norm_nonneg _) (hB1 0 hmem0)
  refine ⟨B1 + 2 * B0 + 1, by linarith, ?_⟩
  intro T hT ψ hψ hnorm hinit s hs
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hnorm1 : ∀ t, ‖ψ t‖ = 1 := fun t => (norm_psi_const hHsa hψ t).trans hnorm
  set X := katoX H P P₁ Ev with hX
  set Y := katoX' H H' P P₁ P₂ Ev Ev' with hY
  set a : ℂ := 1 / (Complex.I * (T : ℂ)) with ha
  have hIT : (Complex.I * (T : ℂ)) ≠ 0 := by
    simp [Complex.ext_iff, ne_of_gt hT0]
  have haIT : a * (Complex.I * (T : ℂ)) = 1 := by
    rw [ha, one_div, inv_mul_cancel₀ hIT]
  have hanorm : ‖a‖ = 1 / T := by
    rw [ha, norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hT0]
  set g : ℝ → ℂ := fun t => ⟪ψ t, ((1 : E →L[ℂ] E) - P t) (ψ t)⟫_ℂ + a * ⟪ψ t, X t (ψ t)⟫_ℂ
    with hgdef
  set g' : ℝ → ℂ := fun t => a * ⟪ψ t, Y t (ψ t)⟫_ℂ with hg'def
  -- the derivative of `g`
  have hgd : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have hQ : HasDerivAt (fun r => (1 : E →L[ℂ] E) - P r) (-P₁ t) t := by
      simpa using (hasDerivAt_const t (1 : E →L[ℂ] E)).sub (hP t)
    have hcommQ : H t * ((1 : E →L[ℂ] E) - P t) - ((1 : E →L[ℂ] E) - P t) * H t = 0 := by
      rw [mul_sub, sub_mul, mul_one, one_mul, heig t, proj_mul_ham hHsa hPsa heig t]
      abel
    have h1 := hasDerivAt_inner_apply hHsa hψ (A := fun r => (1 : E →L[ℂ] E) - P r)
      (A' := fun r => -P₁ r) hQ
    rw [hcommQ] at h1
    have h2 := hasDerivAt_inner_apply hHsa hψ (A := X) (A' := Y)
      (hasDerivAt_katoX hH hEv hP hP1 hgap t)
    rw [hX, hY, commutator_katoX hHsa hPsa hPidem heig hgap hP t] at h2
    have h3 := h1.add (h2.const_mul a)
    convert h3 using 1
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, ContinuousLinearMap.zero_apply,
      inner_zero_right, mul_zero, add_zero]
    linear_combination (-(⟪ψ t, P₁ t (ψ t)⟫_ℂ)) * haIT
  -- bound on the derivative
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g' t‖ ≤ B1 / T := by
    intro t ht
    have h1 : ‖⟪ψ t, Y t (ψ t)⟫_ℂ‖ ≤ B1 := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      have := (Y t).le_opNorm (ψ t)
      rw [hnorm1 t] at this ⊢
      simpa using le_trans this (by simpa [hnorm1 t] using hB1 t ht)
    rw [hg'def]
    simp only [norm_mul, hanorm]
    rw [div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right h1 hT0.le
  -- mean value inequality
  have hmvt : ‖g s - g 0‖ ≤ (B1 / T) * ‖s - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hgd t).hasDerivWithinAt) hbound (convex_Icc 0 1) hmem0 hs
  have hs1 : ‖s - (0 : ℝ)‖ ≤ 1 := by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hmvt' : ‖g s - g 0‖ ≤ B1 / T := by
    refine le_trans hmvt ?_
    have : (B1 / T) * ‖s - (0 : ℝ)‖ ≤ (B1 / T) * 1 :=
      mul_le_mul_of_nonneg_left hs1 (div_nonneg hB1nn (le_of_lt hT0))
    simpa using this
  -- the expectation of the projection is the squared error
  have hkey : ∀ t, ⟪ψ t, ((1 : E →L[ℂ] E) - P t) (ψ t)⟫_ℂ = ((‖ψ t - P t (ψ t)‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    have hadj : ContinuousLinearMap.adjoint ((1 : E →L[ℂ] E) - P t) = (1 : E →L[ℂ] E) - P t := by
      have h2 := (hPsa t).star_eq
      rw [ContinuousLinearMap.star_eq_adjoint] at h2
      rw [map_sub, h2]
      congr 1
      simpa using (ContinuousLinearMap.star_eq_adjoint (1 : E →L[ℂ] E)).symm
    have hQQ : ((1 : E →L[ℂ] E) - P t) * ((1 : E →L[ℂ] E) - P t) = (1 : E →L[ℂ] E) - P t := by
      have hexpand : ((1 : E →L[ℂ] E) - P t) * ((1 : E →L[ℂ] E) - P t)
          = 1 - P t - P t + P t * P t := by noncomm_ring
      rw [hexpand, hPidem t]
      abel
    have hap : ((1 : E →L[ℂ] E) - P t) (ψ t) = ψ t - P t (ψ t) := by simp
    calc ⟪ψ t, ((1 : E →L[ℂ] E) - P t) (ψ t)⟫_ℂ
        = ⟪ψ t, (((1 : E →L[ℂ] E) - P t) * ((1 : E →L[ℂ] E) - P t)) (ψ t)⟫_ℂ := by rw [hQQ]
      _ = ⟪ψ t, ContinuousLinearMap.adjoint ((1 : E →L[ℂ] E) - P t)
            (((1 : E →L[ℂ] E) - P t) (ψ t))⟫_ℂ := by rw [hadj]; rfl
      _ = ⟪((1 : E →L[ℂ] E) - P t) (ψ t), ((1 : E →L[ℂ] E) - P t) (ψ t)⟫_ℂ :=
            ContinuousLinearMap.adjoint_inner_right _ _ _
      _ = ((‖ψ t - P t (ψ t)‖ ^ 2 : ℝ) : ℂ) := by
            rw [hap, inner_self_eq_norm_sq_to_K]; norm_cast
  have hg0 : g 0 = a * ⟪ψ 0, X 0 (ψ 0)⟫_ℂ := by
    have : ((1 : E →L[ℂ] E) - P 0) (ψ 0) = 0 := by simp [hinit]
    rw [hgdef]
    simp [this]
  have hXbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖a * ⟪ψ t, X t (ψ t)⟫_ℂ‖ ≤ B0 / T := by
    intro t ht
    have h1 : ‖⟪ψ t, X t (ψ t)⟫_ℂ‖ ≤ B0 := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      have h2 := (X t).le_opNorm (ψ t)
      rw [hnorm1 t] at h2 ⊢
      simpa using le_trans h2 (by simpa [hnorm1 t] using hB0 t ht)
    rw [norm_mul, hanorm, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right h1 hT0.le
  -- put everything together
  have hexp : ⟪ψ s, ((1 : E →L[ℂ] E) - P s) (ψ s)⟫_ℂ
      = (g s - g 0) + g 0 - a * ⟪ψ s, X s (ψ s)⟫_ℂ := by
    rw [hgdef]; ring
  have hfinal : ‖⟪ψ s, ((1 : E →L[ℂ] E) - P s) (ψ s)⟫_ℂ‖ ≤ B1 / T + B0 / T + B0 / T := by
    rw [hexp]
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hmvt' ?_)) (hXbound s hs)
    rw [hg0]
    exact hXbound 0 hmem0
  rw [hkey s, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hfinal
  have : B1 / T + B0 / T + B0 / T = (B1 + 2 * B0) / T := by ring
  rw [this] at hfinal
  exact le_trans hfinal (div_le_div_of_nonneg_right (by linarith) hT0.le)

end

end Phys

