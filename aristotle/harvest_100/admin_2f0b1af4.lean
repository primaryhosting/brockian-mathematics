/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace Phys

/-! ## The pure ring algebra behind Kato's construction -/

/-- The algebraic heart of the adiabatic theorem.  In a ring, let `p` be an idempotent,
`k` an element annihilating `p` on both sides (think of `k = H - E` with `p` the spectral
projection of the eigenvalue `E`), `d` the derivative of `p` (so that `d = d*p + p*d`), and `b`
a two-sided inverse of `k + p`.  Then the explicitly constructed element
`b*(1-p)*d*p - p*d*(1-p)*b` has commutator with `k` equal to `d`. -/
theorem kato_commutator {R : Type*} [Ring R] {k p d b : R}
    (hp : p * p = p) (hkp : k * p = 0) (hpk : p * k = 0)
    (hd : d = d * p + p * d) (hb1 : b * (k + p) = 1) (hb2 : (k + p) * b = 1) :
    k * (b * (1 - p) * d * p - p * d * (1 - p) * b)
      - (b * (1 - p) * d * p - p * d * (1 - p) * b) * k = d := by
  have e1 : p * (k + p) = p := by rw [mul_add, hpk, hp, zero_add]
  have hpb : p * b = p := by conv_lhs => rw [← e1, mul_assoc, hb2, mul_one]
  have e2 : (k + p) * p = p := by rw [add_mul, hkp, hp, zero_add]
  have hbp : b * p = p := by conv_lhs => rw [← e2, ← mul_assoc, hb1, one_mul]
  have hkb : k * b = 1 - p := by
    have h := hb2; rw [add_mul, hpb] at h; exact eq_sub_of_add_eq h
  have hbk : b * k = 1 - p := by
    have h := hb1; rw [mul_add, hbp] at h; exact eq_sub_of_add_eq h
  have hpdp : p * d * p = 0 := by
    have h : p * d * p = p * d * p + p * d * p := by
      conv_lhs => rw [hd]
      have e : p * (d * p + p * d) * p = p * d * (p * p) + (p * p) * d * p := by noncomm_ring
      rw [e, hp]
    have h' : p * d * p + 0 = p * d * p + p * d * p := by simpa using h
    exact (add_left_cancel h').symm
  have hA : (1 - p) * (1 - p) = 1 - p := by
    have e : (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
    rw [e, hp]; abel
  have t1 : (1 - p) * ((1 - p) * d * p) = d * p := by
    rw [show (1 - p) * ((1 - p) * d * p) = ((1 - p) * (1 - p)) * d * p by noncomm_ring, hA,
      show (1 - p) * d * p = d * p - p * d * p by noncomm_ring, hpdp, sub_zero]
  have t4 : (p * d * (1 - p)) * (1 - p) = p * d := by
    rw [show (p * d * (1 - p)) * (1 - p) = p * d * ((1 - p) * (1 - p)) by noncomm_ring, hA,
      show p * d * (1 - p) = p * d - p * d * p by noncomm_ring, hpdp, sub_zero]
  have key : k * (b * (1 - p) * d * p - p * d * (1 - p) * b)
      - (b * (1 - p) * d * p - p * d * (1 - p) * b) * k
      = (k * b) * ((1 - p) * d * p) - (k * p) * (d * (1 - p) * b)
        - (b * (1 - p) * d) * (p * k) + (p * d * (1 - p)) * (b * k) := by noncomm_ring
  rw [key, hkb, hkp, hbk, hpk, t1, t4]
  simp
  conv_rhs => rw [hd]

/-! ## The adiabatic setting -/

section Adiabatic

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [FiniteDimensional ℂ 𝓗]

/-- The shifted Hamiltonian `H(s) - E(s)`. -/
noncomputable def shiftedHam (Ham : ℝ → (𝓗 →L[ℂ] 𝓗)) (Ev : ℝ → ℝ) (s : ℝ) : 𝓗 →L[ℂ] 𝓗 :=
  Ham s - (Ev s : ℂ) • (1 : 𝓗 →L[ℂ] 𝓗)

/-- `H(s) - E(s) + P(s)`: invertible precisely because `E(s)` is an isolated eigenvalue. -/
noncomputable def gappedOp (Ham P : ℝ → (𝓗 →L[ℂ] 𝓗)) (Ev : ℝ → ℝ) (s : ℝ) : 𝓗 →L[ℂ] 𝓗 :=
  shiftedHam Ham Ev s + P s

/-- The inverse of `gappedOp`; on the range of `1 - P(s)` it is the reduced resolvent
`((H(s) - E(s))|_{ran (1-P)})⁻¹`. -/
noncomputable def reducedResolvent (Ham P : ℝ → (𝓗 →L[ℂ] 𝓗)) (Ev : ℝ → ℝ) (s : ℝ) :
    𝓗 →L[ℂ] 𝓗 :=
  Ring.inverse (gappedOp Ham P Ev s)

/-- Kato's auxiliary observable, an explicit solution of the commutator equation
`[H(s), X(s)] = -i P'(s)`. -/
noncomputable def katoObs (Ham P : ℝ → (𝓗 →L[ℂ] 𝓗)) (Ev : ℝ → ℝ) (s : ℝ) : 𝓗 →L[ℂ] 𝓗 :=
  -Complex.I • (reducedResolvent Ham P Ev s * (1 - P s) * deriv P s * P s
    - P s * deriv P s * (1 - P s) * reducedResolvent Ham P Ev s)

variable (Ham P : ℝ → (𝓗 →L[ℂ] 𝓗)) (Ev : ℝ → ℝ) (gap : ℝ)

/-- The gap condition makes `H(s) - E(s) + P(s)` invertible. -/
lemma isUnit_gappedOp
    (hP_idem : ∀ s, P s * P s = P s)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖) (s : ℝ) :
    IsUnit (gappedOp Ham P Ev s) := by
  have key : ∀ v : 𝓗, gappedOp Ham P Ev s v = 0 → v = 0 := by
    intro v hv
    have happ : Ham s v - (Ev s : ℂ) • v + P s v = 0 := by
      simpa [gappedOp, shiftedHam] using hv
    have hPv : P s v = 0 := by
      have h0 := congrArg (fun w => P s w) happ
      simp only [map_add, map_sub, map_smul, map_zero] at h0
      have h1 : P s (Ham s v) = (Ev s : ℂ) • P s v := by
        have := congrArg (fun (A : 𝓗 →L[ℂ] 𝓗) => A v) ((hComm s).symm.trans (hEig s))
        simpa using this
      have h2 : P s (P s v) = P s v := by
        have := congrArg (fun (A : 𝓗 →L[ℂ] 𝓗) => A v) (hP_idem s)
        simpa using this
      rw [h1, h2] at h0
      simpa using h0
    have h3 : Ham s v - (Ev s : ℂ) • v = 0 := by rw [hPv, add_zero] at happ; exact happ
    have hgv := hgap s v hPv
    rw [h3] at hgv
    simp at hgv
    have hle : ‖v‖ ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [hgv]
    simpa using le_antisymm hle (norm_nonneg v)
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj : Function.Injective ((gappedOp Ham P Ev s) : 𝓗 →ₗ[ℂ] 𝓗) := by
    intro x y hxy
    have h0 : gappedOp Ham P Ev s (x - y) = 0 := by simpa [map_sub, sub_eq_zero] using hxy
    exact sub_eq_zero.mp (key _ h0)
  exact ⟨hinj, (LinearMap.injective_iff_surjective).1 hinj⟩

omit [FiniteDimensional ℂ 𝓗] in
lemma contDiff_gappedOp (hHam : ContDiff ℝ 1 Ham) (hEv : ContDiff ℝ 1 Ev)
    (hP : ContDiff ℝ 1 P) : ContDiff ℝ 1 (gappedOp Ham P Ev) := by
  have h1 : ContDiff ℝ 1 (fun s => ((Ev s : ℂ)) • (1 : 𝓗 →L[ℂ] 𝓗)) :=
    ContDiff.smul (Complex.ofRealCLM.contDiff.comp hEv) contDiff_const
  exact (hHam.sub h1).add hP

lemma contDiff_reducedResolvent
    (hP_idem : ∀ s, P s * P s = P s)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖)
    (hHam : ContDiff ℝ 1 Ham) (hEv : ContDiff ℝ 1 Ev) (hP : ContDiff ℝ 1 P) :
    ContDiff ℝ 1 (reducedResolvent Ham P Ev) := by
  have hM : ContDiff ℝ 1 (gappedOp Ham P Ev) := contDiff_gappedOp Ham P Ev hHam hEv hP
  rw [contDiff_iff_contDiffAt]
  intro s
  obtain ⟨u, hu⟩ := isUnit_gappedOp Ham P Ev gap hP_idem hEig hComm hgap_pos hgap s
  have h1 : ContDiffAt ℝ 1 (Ring.inverse : (𝓗 →L[ℂ] 𝓗) → (𝓗 →L[ℂ] 𝓗)) (gappedOp Ham P Ev s) := by
    rw [← hu]; exact contDiffAt_ringInverse ℝ u
  exact h1.comp s hM.contDiffAt

lemma contDiff_katoObs
    (hP_idem : ∀ s, P s * P s = P s)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖)
    (hHam : ContDiff ℝ 1 Ham) (hEv : ContDiff ℝ 1 Ev) (hP : ContDiff ℝ 2 P) :
    ContDiff ℝ 1 (katoObs Ham P Ev) := by
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by norm_num)
  have hB : ContDiff ℝ 1 (reducedResolvent Ham P Ev) :=
    contDiff_reducedResolvent Ham P Ev gap hP_idem hEig hComm hgap_pos hgap hHam hEv hP1
  have h : ContDiff ℝ (1 + 1 : ℕ) P := by exact_mod_cast hP
  have hdP : ContDiff ℝ 1 (deriv P) := ((contDiff_succ_iff_deriv (n := (1 : ℕ))).1 h).2.2
  have hQ : ContDiff ℝ 1 (fun s => (1 : 𝓗 →L[ℂ] 𝓗) - P s) := contDiff_const.sub hP1
  exact ContDiff.const_smul _
    (((hB.mul hQ).mul hdP).mul hP1 |>.sub (((hP1.mul hdP).mul hQ).mul hB))

omit [FiniteDimensional ℂ 𝓗] in
/-- `P' = P' P + P P'`, obtained by differentiating `P² = P`. -/
lemma deriv_proj_eq (hP_idem : ∀ s, P s * P s = P s) (hP : ContDiff ℝ 1 P) (s : ℝ) :
    deriv P s = deriv P s * P s + P s * deriv P s := by
  have hdP : HasDerivAt P (deriv P s) s := (hP.differentiable (by norm_num) s).hasDerivAt
  have h2 : HasDerivAt (fun t => P t * P t) (deriv P s * P s + P s * deriv P s) s := hdP.mul hdP
  have h3 : (fun t => P t * P t) = P := funext hP_idem
  rw [h3] at h2
  exact hdP.unique h2

/-- Kato's observable solves the commutator equation `[H, X] = -i P'`. -/
lemma commutator_katoObs
    (hP_idem : ∀ s, P s * P s = P s)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖)
    (hP : ContDiff ℝ 1 P) (s : ℝ) :
    Ham s * katoObs Ham P Ev s - katoObs Ham P Ev s * Ham s
      = -Complex.I • deriv P s := by
  have hkp : shiftedHam Ham Ev s * P s = 0 := by
    rw [shiftedHam, sub_mul, hEig s, smul_mul_assoc, one_mul, sub_self]
  have hpk : P s * shiftedHam Ham Ev s = 0 := by
    rw [shiftedHam, mul_sub, ← hComm s, hEig s, mul_smul_comm, mul_one, sub_self]
  have hunit := isUnit_gappedOp Ham P Ev gap hP_idem hEig hComm hgap_pos hgap s
  have hb1 : reducedResolvent Ham P Ev s * (shiftedHam Ham Ev s + P s) = 1 := by
    rw [reducedResolvent]
    exact Ring.inverse_mul_cancel _ hunit
  have hb2 : (shiftedHam Ham Ev s + P s) * reducedResolvent Ham P Ev s = 1 := by
    rw [reducedResolvent]
    exact Ring.mul_inverse_cancel _ hunit
  have hd := deriv_proj_eq P hP_idem hP s
  have key := kato_commutator (hP_idem s) hkp hpk hd hb1 hb2
  have hHam_eq : Ham s = shiftedHam Ham Ev s + (Ev s : ℂ) • (1 : 𝓗 →L[ℂ] 𝓗) := by
    rw [shiftedHam, sub_add_cancel]
  rw [katoObs]
  set y : 𝓗 →L[ℂ] 𝓗 :=
    reducedResolvent Ham P Ev s * (1 - P s) * deriv P s * P s
      - P s * deriv P s * (1 - P s) * reducedResolvent Ham P Ev s with hy
  have hcomm : Ham s * (-Complex.I • y) - (-Complex.I • y) * Ham s
      = -Complex.I • (shiftedHam Ham Ev s * y - y * shiftedHam Ham Ev s) := by
    rw [hHam_eq]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, one_mul,
      mul_one]
    module
  rw [hcomm, key]

/-- Derivative of the expectation value `⟪ψ, A ψ⟫` along a solution of the Schrödinger
equation `i ε ψ' = H ψ`. -/
lemma hasDerivAt_expectation {ε : ℝ} (A : ℝ → (𝓗 →L[ℂ] 𝓗)) (A' : 𝓗 →L[ℂ] 𝓗)
    (hHam_sa : ∀ s, IsSelfAdjoint (Ham s)) (psi : ℝ → 𝓗) (s : ℝ)
    (hpsi : HasDerivAt psi (-(Complex.I / ε) • (Ham s (psi s))) s)
    (hA : HasDerivAt A A' s) :
    HasDerivAt (fun t => ⟪psi t, A t (psi t)⟫_ℂ)
      (⟪psi s, A' (psi s)⟫_ℂ
        + (Complex.I / ε) * ⟪psi s, ((Ham s * A s - A s * Ham s) (psi s))⟫_ℂ) s := by
  have hR : HasDerivAt (fun t => (A t).restrictScalars ℝ) (A'.restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ 𝓗 𝓗 ℝ ℝ).hasFDerivAt.comp_hasDerivAt s hA
  have h1 : HasDerivAt (fun t => A t (psi t))
      (A' (psi s) + A s (-(Complex.I / ε) • (Ham s (psi s)))) s := hR.clm_apply hpsi
  have h2 := hpsi.inner ℂ h1
  convert h2 using 1
  have hsaa : ∀ x y : 𝓗, ⟪Ham s x, y⟫_ℂ = ⟪x, Ham s y⟫_ℂ := by
    intro x y; rw [← ContinuousLinearMap.adjoint_inner_left, (hHam_sa s).adjoint_eq]
  simp only [inner_add_right, inner_smul_left, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, inner_sub_right, map_smul, inner_smul_right]
  rw [hsaa]
  simp [Complex.conj_I]
  ring

/-- Conservation of the norm along the Schrödinger flow. -/
lemma norm_psi_eq {ε : ℝ} (hHam_sa : ∀ s, IsSelfAdjoint (Ham s)) (psi : ℝ → 𝓗)
    (hpsi : ∀ s, HasDerivAt psi (-(Complex.I / ε) • (Ham s (psi s))) s)
    (hpsi0 : ‖psi 0‖ = 1) (s : ℝ) : ‖psi s‖ = 1 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u => ⟪psi u, psi u⟫_ℂ) 0 t := by
    intro t
    have h := hasDerivAt_expectation Ham (fun _ => (1 : 𝓗 →L[ℂ] 𝓗)) 0 hHam_sa psi t (hpsi t)
      (hasDerivAt_const t (1 : 𝓗 →L[ℂ] 𝓗))
    simpa using h
  have hdiff : Differentiable ℝ (fun u => ⟪psi u, psi u⟫_ℂ) := fun t => (hd t).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t => (hd t).deriv) s 0
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hpsi0] at hconst
  have h2 : (‖psi s‖ : ℝ) ^ 2 = 1 ^ 2 := by exact_mod_cast hconst
  nlinarith [norm_nonneg (psi s)]

/-- **Adiabatic theorem.**  Let `s ↦ H(s)` be a `C¹` family of self-adjoint Hamiltonians on a
finite-dimensional complex Hilbert space, and let `P(s)` be a `C²` family of rank-one
(i.e. nondegenerate) orthogonal spectral projections for an eigenvalue `E(s)` that is
separated from the rest of the spectrum by a uniform gap `gap > 0`.  Then there is a constant
`C`, depending only on the family, such that every solution of the Schrödinger equation
`i ε ψ'(s) = H(s) ψ(s)` starting in the eigenspace of `H(0)` stays within `C √ε` of the
instantaneous eigenspace of `H(s)` for all `s ∈ [0,1]`: the state is dragged along with the
slowly varying eigenspace.  (Physical time is `t = s/ε`, so `ε → 0` is exactly the
slowly-varying limit.)

The nondegeneracy hypothesis `hP_rank` is included because it is part of the physical
statement; the proof only uses that `P s` is an orthogonal projection onto an eigenspace
separated by a gap.  The solution `psi` is assumed to solve the Schrödinger equation on all
of `ℝ`, which is no restriction: the Hamiltonian family is globally `C¹`, so solutions of
this linear equation extend to all of `ℝ`.  See `Phys.adiabatic_hypotheses_satisfiable` for
a model satisfying all the hypotheses. -/
theorem adiabatic_theorem
    (hHam_sa : ∀ s, IsSelfAdjoint (Ham s))
    (hP_sa : ∀ s, IsSelfAdjoint (P s))
    (hP_idem : ∀ s, P s * P s = P s)
    (hP_rank : ∀ s, Module.finrank ℂ (LinearMap.range (P s : 𝓗 →ₗ[ℂ] 𝓗)) = 1)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖)
    (hHam_smooth : ContDiff ℝ 1 Ham) (hEv_smooth : ContDiff ℝ 1 Ev)
    (hP_smooth : ContDiff ℝ 2 P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ psi : ℝ → 𝓗,
      (∀ s, HasDerivAt psi (-(Complex.I / ε) • (Ham s (psi s))) s) →
      ‖psi 0‖ = 1 → P 0 (psi 0) = psi 0 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖psi s - P s (psi s)‖ ≤ C * Real.sqrt ε := by
  have hP1 : ContDiff ℝ 1 P := hP_smooth.of_le (by norm_num)
  have hX : ContDiff ℝ 1 (katoObs Ham P Ev) :=
    contDiff_katoObs Ham P Ev gap hP_idem hEig hComm hgap_pos hgap hHam_smooth hEv_smooth hP_smooth
  obtain ⟨KX, hKX⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hX.continuous.continuousOn
  obtain ⟨KX', hKX'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hX.continuous_deriv le_rfl).continuousOn
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hKX0 : 0 ≤ KX := le_trans (norm_nonneg _) (hKX 0 h0mem)
  have hKX'0 : 0 ≤ KX' := le_trans (norm_nonneg _) (hKX' 0 h0mem)
  refine ⟨Real.sqrt (KX' + 2 * KX), Real.sqrt_nonneg _, ?_⟩
  intro ε hε psi hpsi hpsi0 hpsi0P s hs
  have hεC : ((ε : ℝ) : ℂ) ≠ 0 := by
    simpa using hε.ne'
  have hnorm : ∀ t, ‖psi t‖ = 1 := norm_psi_eq Ham hHam_sa psi hpsi hpsi0
  have hexpec_le : ∀ (A : 𝓗 →L[ℂ] 𝓗) (t : ℝ), ‖⟪psi t, A (psi t)⟫_ℂ‖ ≤ ‖A‖ := by
    intro A t
    calc ‖⟪psi t, A (psi t)⟫_ℂ‖ ≤ ‖psi t‖ * ‖A (psi t)‖ := norm_inner_le_norm _ _
      _ ≤ ‖psi t‖ * (‖A‖ * ‖psi t‖) :=
          mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ := by rw [hnorm t]; ring
  -- derivative of the expectation value of the projection
  have hdP : ∀ t, HasDerivAt (fun u => ⟪psi u, P u (psi u)⟫_ℂ)
      (⟪psi t, deriv P t (psi t)⟫_ℂ) t := by
    intro t
    have h := hasDerivAt_expectation Ham P (deriv P t) hHam_sa psi t (hpsi t)
      ((hP1.differentiable (by norm_num) t).hasDerivAt)
    rw [hComm t, sub_self] at h
    simpa using h
  -- derivative of the expectation value of Kato's observable
  have hdX : ∀ t, HasDerivAt (fun u => ⟪psi u, katoObs Ham P Ev u (psi u)⟫_ℂ)
      (⟪psi t, deriv (katoObs Ham P Ev) t (psi t)⟫_ℂ
        + (1 / (ε : ℂ)) * ⟪psi t, deriv P t (psi t)⟫_ℂ) t := by
    intro t
    have h := hasDerivAt_expectation Ham (katoObs Ham P Ev) (deriv (katoObs Ham P Ev) t)
      hHam_sa psi t (hpsi t) ((hX.differentiable (by norm_num) t).hasDerivAt)
    rw [commutator_katoObs Ham P Ev gap hP_idem hEig hComm hgap_pos hgap hP1 t] at h
    convert h using 1
    rw [ContinuousLinearMap.smul_apply, inner_smul_right]
    field_simp
    rw [mul_comm]
    simp
  -- the corrected quantity `G`, whose derivative is `O(ε)`
  set G : ℝ → ℂ := fun t => ⟪psi t, P t (psi t)⟫_ℂ
    - (ε : ℂ) * ⟪psi t, katoObs Ham P Ev t (psi t)⟫_ℂ with hG
  have hGderiv : ∀ t, HasDerivAt G
      (-((ε : ℂ) * ⟪psi t, deriv (katoObs Ham P Ev) t (psi t)⟫_ℂ)) t := by
    intro t
    have h := (hdP t).sub ((hdX t).const_mul (ε : ℂ))
    convert h using 1
    field_simp
    ring
  -- the derivative bound
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖-((ε : ℂ) * ⟪psi t, deriv (katoObs Ham P Ev) t (psi t)⟫_ℂ)‖ ≤ ε * KX' := by
    intro t ht
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    exact (hexpec_le _ t).trans (hKX' t ht)
  have hMVT : ‖G s - G 0‖ ≤ (ε * KX') * ‖s - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hGderiv t).hasDerivWithinAt) hbound (convex_Icc 0 1) h0mem hs
  have hs1 : ‖s - (0 : ℝ)‖ ≤ 1 := by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hMVT' : ‖G s - G 0‖ ≤ ε * KX' := by
    refine hMVT.trans ?_
    calc (ε * KX') * ‖s - 0‖ ≤ (ε * KX') * 1 :=
          mul_le_mul_of_nonneg_left hs1 (mul_nonneg hε.le hKX'0)
      _ = ε * KX' := mul_one _
  -- expectation of the projection at time 0 is 1
  have hexp0 : ⟪psi 0, P 0 (psi 0)⟫_ℂ = 1 := by
    rw [hpsi0P, inner_self_eq_norm_sq_to_K, hpsi0]
    norm_num
  -- expectation of the projection is the squared norm of the projected state
  have hexps : ⟪psi s, P s (psi s)⟫_ℂ = ((‖P s (psi s)‖ : ℝ) : ℂ) ^ 2 := by
    have h1 : ⟪P s (psi s), P s (psi s)⟫_ℂ = ⟪psi s, P s (psi s)⟫_ℂ := by
      rw [← (hP_sa s).adjoint_eq, ContinuousLinearMap.adjoint_inner_left, (hP_sa s).adjoint_eq]
      have := congrArg (fun (A : 𝓗 →L[ℂ] 𝓗) => A (psi s)) (hP_idem s)
      simpa using congrArg (fun w => ⟪psi s, w⟫_ℂ) this
    rw [← h1, inner_self_eq_norm_sq_to_K]
    norm_cast
  -- bounding the deviation of the expectation value from 1
  have hXbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(ε : ℂ) * ⟪psi t, katoObs Ham P Ev t (psi t)⟫_ℂ‖ ≤ ε * KX := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    exact (hexpec_le _ t).trans (hKX t ht)
  have hsplit : ⟪psi s, P s (psi s)⟫_ℂ - ⟪psi 0, P 0 (psi 0)⟫_ℂ
      = (G s - G 0) + ((ε : ℂ) * ⟪psi s, katoObs Ham P Ev s (psi s)⟫_ℂ)
        - ((ε : ℂ) * ⟪psi 0, katoObs Ham P Ev 0 (psi 0)⟫_ℂ) := by
    rw [hG]; ring
  have hfinal : ‖⟪psi s, P s (psi s)⟫_ℂ - 1‖ ≤ ε * (KX' + 2 * KX) := by
    rw [← hexp0, hsplit]
    calc ‖(G s - G 0) + ((ε : ℂ) * ⟪psi s, katoObs Ham P Ev s (psi s)⟫_ℂ)
            - ((ε : ℂ) * ⟪psi 0, katoObs Ham P Ev 0 (psi 0)⟫_ℂ)‖
        ≤ ‖(G s - G 0) + ((ε : ℂ) * ⟪psi s, katoObs Ham P Ev s (psi s)⟫_ℂ)‖
            + ‖((ε : ℂ) * ⟪psi 0, katoObs Ham P Ev 0 (psi 0)⟫_ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖G s - G 0‖ + ‖((ε : ℂ) * ⟪psi s, katoObs Ham P Ev s (psi s)⟫_ℂ)‖)
            + ‖((ε : ℂ) * ⟪psi 0, katoObs Ham P Ev 0 (psi 0)⟫_ℂ)‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ (ε * KX' + ε * KX) + ε * KX := by
          gcongr
          · exact hXbound s hs
          · exact hXbound 0 h0mem
      _ = ε * (KX' + 2 * KX) := by ring
  -- conclude
  have hnormsq : ‖psi s - P s (psi s)‖ ^ 2 = 1 - ‖P s (psi s)‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), hnorm s, hexps]
    have : (RCLike.re : ℂ → ℝ) (((‖P s (psi s)‖ : ℝ) : ℂ) ^ 2) = ‖P s (psi s)‖ ^ 2 := by
      norm_cast
    rw [this]
    ring
  have hdiffbound : 1 - ‖P s (psi s)‖ ^ 2 ≤ ε * (KX' + 2 * KX) := by
    refine le_trans ?_ hfinal
    rw [hexps]
    have : ((‖P s (psi s)‖ : ℝ) : ℂ) ^ 2 - 1 = (((‖P s (psi s)‖ ^ 2 - 1 : ℝ)) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    cases abs_cases (‖P s (psi s)‖ ^ 2 - 1) with
    | inl h => linarith [h.1]
    | inr h => linarith [h.1]
  have hsq : ‖psi s - P s (psi s)‖ ^ 2 ≤ ε * (KX' + 2 * KX) := by
    rw [hnormsq]; exact hdiffbound
  have hle : ‖psi s - P s (psi s)‖ ≤ Real.sqrt (ε * (KX' + 2 * KX)) := by
    rw [← Real.sqrt_sq (norm_nonneg (psi s - P s (psi s)))]
    exact Real.sqrt_le_sqrt hsq
  calc ‖psi s - P s (psi s)‖ ≤ Real.sqrt (ε * (KX' + 2 * KX)) := hle
    _ = Real.sqrt (KX' + 2 * KX) * Real.sqrt ε := by
        rw [mul_comm, Real.sqrt_mul (by positivity)]

end Adiabatic

/-! ## The hypotheses of the adiabatic theorem are satisfiable

A two-level system with the (constant) spectral projection onto the first basis vector and
the Hamiltonian `2 P - 1`, whose eigenvalue `1` on the range of `P` is nondegenerate and
separated from the eigenvalue `-1` by the gap `2`. -/

/-- A qubit: the two-dimensional complex Hilbert space. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The first basis vector of the qubit. -/
noncomputable def qubitVec : Qubit := EuclideanSpace.single 0 (1 : ℂ)

/-- The orthogonal projection onto the line spanned by `qubitVec`. -/
noncomputable def qubitProj : Qubit →L[ℂ] Qubit := (innerSL ℂ qubitVec).smulRight qubitVec

/-- The Hamiltonian `2 P - 1`, with nondegenerate eigenvalue `1` and gap `2`. -/
noncomputable def qubitHam : Qubit →L[ℂ] Qubit := (2 : ℂ) • qubitProj - 1

/-- The hypotheses of `Phys.adiabatic_theorem` are satisfiable, so the theorem is not
vacuous. -/
theorem adiabatic_hypotheses_satisfiable :
    ∃ (Ham P : ℝ → (Qubit →L[ℂ] Qubit)) (Ev : ℝ → ℝ) (gap : ℝ),
      (∀ s, IsSelfAdjoint (Ham s)) ∧ (∀ s, IsSelfAdjoint (P s)) ∧
      (∀ s, P s * P s = P s) ∧
      (∀ s, Module.finrank ℂ (LinearMap.range (P s : Qubit →ₗ[ℂ] Qubit)) = 1) ∧
      (∀ s, Ham s * P s = (Ev s : ℂ) • P s) ∧ (∀ s, Ham s * P s = P s * Ham s) ∧
      0 < gap ∧
      (∀ s, ∀ v : Qubit, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖) ∧
      ContDiff ℝ 1 Ham ∧ ContDiff ℝ 1 Ev ∧ ContDiff ℝ 2 P := by
  have hnorm0 : ‖qubitVec‖ = 1 := by simp [qubitVec]
  have hidem : qubitProj * qubitProj = qubitProj := by
    ext v
    simp [qubitProj, hnorm0]
  have hPsa : IsSelfAdjoint qubitProj := by
    have h : qubitProj = ContinuousLinearMap.adjoint qubitProj := by
      refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 ?_
      intro x y
      simp [qubitProj, inner_smul_left, inner_smul_right, mul_comm]
    exact (h.symm : ContinuousLinearMap.adjoint qubitProj = qubitProj)
  have hHsa : IsSelfAdjoint qubitHam := by
    have h : qubitHam = ContinuousLinearMap.adjoint qubitHam := by
      refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 ?_
      intro x y
      simp [qubitHam, qubitProj, inner_smul_left, inner_smul_right, inner_sub_left,
        inner_sub_right, mul_comm, Complex.conj_ofNat]
    exact (h.symm : ContinuousLinearMap.adjoint qubitHam = qubitHam)
  have hrank : Module.finrank ℂ (LinearMap.range (qubitProj : Qubit →ₗ[ℂ] Qubit)) = 1 := by
    have hrange : LinearMap.range (qubitProj : Qubit →ₗ[ℂ] Qubit)
        = Submodule.span ℂ {qubitVec} := by
      apply le_antisymm
      · rintro x ⟨v, rfl⟩
        exact Submodule.mem_span_singleton.2 ⟨⟪qubitVec, v⟫_ℂ, rfl⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact ⟨qubitVec, by simp [qubitProj, hnorm0]⟩
    rw [hrange, finrank_span_singleton]
    simp [qubitVec]
  refine ⟨fun _ => qubitHam, fun _ => qubitProj, fun _ => 1, 2, fun _ => hHsa, fun _ => hPsa,
    fun _ => hidem, fun _ => hrank, ?_, ?_, by norm_num, ?_, contDiff_const, contDiff_const,
    contDiff_const⟩
  · intro _
    simp only [qubitHam, sub_mul, smul_mul_assoc, hidem, one_mul]
    push_cast
    module
  · intro _
    simp only [qubitHam, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hidem, one_mul, mul_one]
  · intro _ v hv
    have hv2 : qubitHam v - ((1 : ℝ) : ℂ) • v = (-2 : ℂ) • v := by
      simp only [qubitHam, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, hv, smul_zero]
      push_cast
      module
    rw [hv2, norm_smul]
    simp

end Phys

