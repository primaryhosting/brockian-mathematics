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

set_option grind.warning false

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A homogeneous linear ODE `w' t = A t (w t)` with continuous (operator valued) coefficient
and vanishing initial datum has only the zero solution. -/
theorem eq_zero_of_linear_ode {A : ℝ → (E →L[ℂ] E)} (hA : Continuous A) {w : ℝ → E}
    (hw : ∀ t, HasDerivAt w (A t (w t)) t) {t₀ : ℝ} (h0 : w t₀ = 0) (t : ℝ) : w t = 0 := by
  set a : ℝ := min t t₀ - 1 with ha
  set b : ℝ := max t t₀ + 1 with hb
  have hab : a ≤ b := by
    have h1 : min t t₀ ≤ max t t₀ := min_le_max
    simp only [ha, hb]; linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hA.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (A a)) (hC a ⟨le_rfl, hab⟩)
  have hmemIoo : ∀ x : ℝ, x ∈ Set.Ioo a b → x ∈ Set.Icc a b := fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hlip : ∀ s ∈ Set.Ioo a b,
      LipschitzOnWith ⟨C, hC0⟩ (fun x : E => A s x) (Set.univ : Set E) := by
    intro s hs
    refine (LipschitzWith.weaken (A s).lipschitz ?_).lipschitzOnWith
    exact hC s (hmemIoo s hs)
  have ht₀ : t₀ ∈ Set.Ioo a b := by
    constructor
    · have : min t t₀ ≤ t₀ := min_le_right _ _
      simp only [ha]; linarith
    · have : t₀ ≤ max t t₀ := le_max_right _ _
      simp only [hb]; linarith
  have htmem : t ∈ Set.Ioo a b := by
    constructor
    · have : min t t₀ ≤ t := min_le_left _ _
      simp only [ha]; linarith
    · have : t ≤ max t t₀ := le_max_left _ _
      simp only [hb]; linarith
  have key : Set.EqOn w (fun _ : ℝ => (0 : E)) (Set.Ioo a b) := by
    refine ODE_solution_unique_of_mem_Ioo (v := fun s x => A s x) (s := fun _ => Set.univ)
      hlip ht₀ (fun s _ => ⟨hw s, Set.mem_univ _⟩) (fun s _ => ⟨?_, Set.mem_univ _⟩) (by simp [h0])
    simpa using hasDerivAt_const s (0 : E)
  simpa using key htmem

/-- **Adiabatic theorem** (Kato's exact formulation).

`H t` is a (bounded, self-adjoint) time-dependent Hamiltonian on a complex Hilbert space `E`,
whose instantaneous, *nondegenerate* eigenvalue `Ev t` has the one-dimensional eigenspace
spanned by the unit vector `e t`; `P t v = ⟪e t, v⟫ • e t` is the corresponding rank-one
spectral projection, and `P' t` is its derivative.

The state `psi` evolves under the adiabatic (slow) dynamics with slowness parameter `ε > 0`:
`ε ψ'(t) = -i H(t) ψ(t) + ε [P'(t), P(t)] ψ(t)`, i.e. the Schrödinger equation on the slow
time scale, corrected by Kato's geometric term `[P' t, P t] = P' t P t - P t P' t`, which is
exactly the generator obtained in the adiabatic limit of a slowly varying Hamiltonian.

Conclusion: a state started in the eigenstate `e 0` stays, for all times, inside the
instantaneous eigenspace: `psi t` is fixed by `P t`, it is an instantaneous eigenvector of
`H t` for the instantaneous eigenvalue `Ev t`, and it remains a multiple of `e t`. -/
theorem adiabatic_theorem [CompleteSpace E]
    (ε : ℝ) (hε : 0 < ε)
    (H P P' : ℝ → (E →L[ℂ] E)) (e : ℝ → E) (Ev : ℝ → ℂ) (psi : ℝ → E)
    (hHc : Continuous H) (hP'c : Continuous P')
    (hHsa : ∀ t, IsSelfAdjoint (H t))
    (he : ∀ t, ‖e t‖ = 1)
    (hHe : ∀ t, H t (e t) = Ev t • e t)
    (hPe : ∀ t v, P t v = ⟪e t, v⟫_ℂ • e t)
    (hPd : ∀ t, HasDerivAt P (P' t) t)
    (hpsi0 : psi 0 = e 0)
    (hpsi : ∀ t, HasDerivAt (fun s => (ε : ℂ) • psi s)
      ((-Complex.I) • H t (psi t) +
        (ε : ℂ) • (P' t (P t (psi t)) - P t (P' t (psi t)))) t) :
    ∀ t, P t (psi t) = psi t ∧ H t (psi t) = Ev t • psi t ∧ ∃ c : ℂ, psi t = c • e t := by
  have hεne : (ε : ℂ) ≠ 0 := by
    simpa using hε.ne'
  -- the generator of the adiabatic evolution
  set c : ℂ := -(Complex.I / (ε : ℂ)) with hc
  set A : ℝ → (E →L[ℂ] E) := fun t => c • H t + (P' t * P t - P t * P' t) with hA
  -- `P` is a family of projections
  have hidem : ∀ t, P t * P t = P t := by
    intro t
    ext v
    have h1 : ⟪e t, e t⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he t]; norm_num
    simp only [ContinuousLinearMap.mul_apply, hPe t, inner_smul_right, h1]
    simp
  -- differentiating `P * P = P`
  have hPP' : ∀ t, P' t * P t + P t * P' t = P' t := by
    intro t
    have h1 : HasDerivAt (fun y => P y * P y)
        (P' t * P t + P t * P' t) t := (hPd t).mul (hPd t)
    have h2 : (fun y => P y * P y) = P := by
      funext y; exact hidem y
    rw [h2] at h1
    exact h1.unique (hPd t)
  have hPP'P : ∀ t, P t * P' t * P t = 0 := by
    intro t
    have h := congrArg (fun X => P t * X) (hPP' t)
    simp only [mul_add, ← mul_assoc, hidem t] at h
    -- h : P * P' * P + P * P' = P * P'
    have : P t * P' t * P t = 0 := by
      have := h
      linear_combination (norm := module) this
    exact this
  -- `P` and `H` commute
  have hEvreal : ∀ t, (starRingEnd ℂ) (Ev t) = Ev t := by
    intro t
    have h1 : ⟪e t, e t⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he t]; norm_num
    have h2 : ⟪e t, H t (e t)⟫_ℂ = Ev t := by
      rw [hHe t, inner_smul_right, h1, mul_one]
    have h3 : ⟪H t (e t), e t⟫_ℂ = (starRingEnd ℂ) (Ev t) := by
      rw [hHe t, inner_smul_left, h1, mul_one]
    have h4 : ⟪H t (e t), e t⟫_ℂ = ⟪e t, H t (e t)⟫_ℂ := by
      have := (hHsa t)
      rw [ContinuousLinearMap.isSelfAdjoint_iff'] at this
      calc ⟪H t (e t), e t⟫_ℂ = ⟪(ContinuousLinearMap.adjoint (H t)) (e t), e t⟫_ℂ := by rw [this]
        _ = ⟪e t, H t (e t)⟫_ℂ := ContinuousLinearMap.adjoint_inner_left _ _ _
    rw [← h3, h4, h2]
  have hcomm : ∀ t, P t * H t = H t * P t := by
    intro t
    ext v
    have hsa : ⟪e t, H t v⟫_ℂ = ⟪H t (e t), v⟫_ℂ := by
      have := (hHsa t)
      rw [ContinuousLinearMap.isSelfAdjoint_iff'] at this
      calc ⟪e t, H t v⟫_ℂ = ⟪(ContinuousLinearMap.adjoint (H t)) (e t), v⟫_ℂ :=
            (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
        _ = ⟪H t (e t), v⟫_ℂ := by rw [this]
    simp only [ContinuousLinearMap.mul_apply, hPe t, hsa, hHe t, inner_smul_left, hEvreal t,
      map_smul, smul_smul, mul_comm]
  -- the key algebraic identity `P' + P A - A P = 0`
  have hkey : ∀ t, P' t + P t * A t - A t * P t = 0 := by
    intro t
    have h1 : P t * A t - A t * P t = -(P' t) := by
      simp only [hA, mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hcomm t]
      have e1 : P t * (P' t * P t) = P t * P' t * P t := by rw [mul_assoc]
      have e2 : P t * (P t * P' t) = P t * P' t := by rw [← mul_assoc, hidem t]
      have e3 : P' t * P t * P t = P' t * P t := by rw [mul_assoc, hidem t]
      have e4 : P t * P' t * P t = 0 := hPP'P t
      rw [e1, e2, e3, e4]
      have := hPP' t
      linear_combination (norm := module) -this
    calc P' t + P t * A t - A t * P t = P' t + (P t * A t - A t * P t) := by abel
      _ = 0 := by rw [h1]; abel
  -- the Schrödinger equation in the form `ψ' = A ψ`
  have hpsi' : ∀ t, HasDerivAt psi (A t (psi t)) t := by
    intro t
    have h : HasDerivAt (fun s => (ε : ℂ)⁻¹ • ((ε : ℂ) • psi s))
        ((ε : ℂ)⁻¹ • ((-Complex.I) • H t (psi t) +
          (ε : ℂ) • (P' t (P t (psi t)) - P t (P' t (psi t))))) t :=
      (hpsi t).const_smul ((ε : ℂ)⁻¹)
    simp only [smul_smul, inv_mul_cancel₀ hεne, one_smul] at h
    have hval : ((ε : ℂ)⁻¹) • ((-Complex.I) • H t (psi t) +
        (ε : ℂ) • (P' t (P t (psi t)) - P t (P' t (psi t)))) = A t (psi t) := by
      simp only [hA, hc, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, smul_add, smul_smul]
      match_scalars <;> field_simp
    rwa [hval] at h
  -- the "leakage" out of the instantaneous eigenspace
  set w : ℝ → E := fun t => P t (psi t) - psi t with hwdef
  have hAcont : Continuous A := by
    have hPc : Continuous P :=
      continuous_iff_continuousAt.2 fun t => (hPd t).continuousAt
    exact ((hHc.const_smul c).add ((hP'c.mul hPc).sub (hPc.mul hP'c)))
  have hwd : ∀ t, HasDerivAt w (A t (w t)) t := by
    intro t
    have hL : HasDerivAt (fun y => (P y).restrictScalars ℝ) ((P' t).restrictScalars ℝ) t :=
      (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hPd t)
    have h1 : HasDerivAt (fun y => P y (psi y)) (P' t (psi t) + P t (A t (psi t))) t :=
      hL.clm_apply (hpsi' t)
    have h2 : HasDerivAt w (P' t (psi t) + P t (A t (psi t)) - A t (psi t)) t :=
      h1.sub (hpsi' t)
    have h3 : P' t (psi t) + P t (A t (psi t)) - A t (psi t) = A t (w t) := by
      have := congrArg (fun X : E →L[ℂ] E => X (psi t)) (hkey t)
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] at this
      simp only [hwdef, map_sub]
      linear_combination (norm := module) this
    rwa [h3] at h2
  have hw0 : w 0 = 0 := by
    simp only [hwdef, hpsi0, sub_eq_zero]
    have h1 : ⟪e 0, e 0⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he 0]; norm_num
    rw [hPe 0, h1, one_smul]
  have hwzero : ∀ t, w t = 0 := fun t => eq_zero_of_linear_ode hAcont hwd hw0 t
  intro t
  have hPfix : P t (psi t) = psi t := by
    have := hwzero t
    simp only [hwdef, sub_eq_zero] at this
    exact this
  refine ⟨hPfix, ?_, ⟨⟪e t, psi t⟫_ℂ, ?_⟩⟩
  · calc H t (psi t) = H t (P t (psi t)) := by rw [hPfix]
      _ = Ev t • (P t (psi t)) := by rw [hPe t, map_smul, hHe t, smul_comm]
      _ = Ev t • psi t := by rw [hPfix]
  · conv_lhs => rw [← hPfix]
    exact hPe t (psi t)

/-- Non-vacuity check: the hypotheses of `Phys.adiabatic_theorem` are satisfiable.
Here `E = ℂ`, the Hamiltonian is the identity with nondegenerate eigenvalue `1` and normalized
eigenvector `1`, and the state is the phase `exp (-(i/ε) t)`. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ, ∃ c : ℂ, Complex.exp (-(Complex.I / (ε : ℂ)) * (t : ℂ)) = c • (1 : ℂ) := by
  have main := adiabatic_theorem (E := ℂ) ε hε
    (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun _ => 0)
    (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
    (fun s => Complex.exp (-(Complex.I / (ε : ℂ)) * (s : ℂ)))
    continuous_const continuous_const (fun _ => IsSelfAdjoint.one _) (by simp)
    (by simp) (by intro t v; simp) (fun _ => hasDerivAt_const _ _) (by simp)
    ?_
  · intro t; exact (main t).2.2
  · intro t
    have hεne : (ε : ℂ) ≠ 0 := by simpa using hε.ne'
    have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ))) 1 t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t))
    have h2 : HasDerivAt (fun s : ℝ => (-(Complex.I / (ε : ℂ))) * (s : ℂ))
        (-(Complex.I / (ε : ℂ))) t := by
      simpa using h1.const_mul (-(Complex.I / (ε : ℂ)))
    have h3 := (h2.cexp).const_smul ((ε : ℂ))
    convert h3 using 1
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
      mul_zero, add_zero, sub_zero, map_zero]
    field_simp

end Phys

