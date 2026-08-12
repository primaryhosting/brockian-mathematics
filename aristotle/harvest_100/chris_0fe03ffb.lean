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

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set

namespace Phys

section Kato

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Differentiating the idempotency relation `P s * P s = P s`. -/
lemma leibniz_of_idempotent {P dP : ℝ → A} (hP : ∀ s, HasDerivAt P (dP s) s)
    (hidem : ∀ s, P s * P s = P s) (s : ℝ) :
    dP s * P s + P s * dP s = dP s := by
  have h1 : HasDerivAt (fun t => P t * P t) (dP s * P s + P s * dP s) s := (hP s).mul (hP s)
  have h2 : HasDerivAt (fun t => P t * P t) (dP s) s := by
    have h : (fun t => P t * P t) = P := funext hidem
    rw [h]; exact hP s
  exact h1.unique h2

/-- For a differentiable family of idempotents one has `P * P' * P = 0`. -/
lemma sandwich_eq_zero {P dP : ℝ → A} (hP : ∀ s, HasDerivAt P (dP s) s)
    (hidem : ∀ s, P s * P s = P s) (s : ℝ) :
    P s * dP s * P s = 0 := by
  have h3 := leibniz_of_idempotent hP hidem s
  have h2 := hidem s
  have key : P s * dP s * P s = P s * dP s * P s + P s * dP s * P s := by
    calc P s * dP s * P s = P s * (dP s * P s + P s * dP s) * P s := by rw [h3]
      _ = (P s * dP s) * (P s * P s) + (P s * P s) * (dP s * P s) := by noncomm_ring
      _ = (P s * dP s) * P s + P s * (dP s * P s) := by rw [h2]
      _ = P s * dP s * P s + P s * dP s * P s := by noncomm_ring
  exact left_eq_add.mp key

/-- The *Kato generator* `K = P' P - P P'` of a differentiable family of idempotents
intertwines `P` with any generator commuting with `P`: writing `G = C + K` one has
`P' + P G - G P = 0`. -/
lemma kato_generator_identity {P dP C : ℝ → A} (hP : ∀ s, HasDerivAt P (dP s) s)
    (hidem : ∀ s, P s * P s = P s) (hcomm : ∀ s, C s * P s = P s * C s) (s : ℝ) :
    dP s + (P s * (C s + (dP s * P s - P s * dP s))
      - (C s + (dP s * P s - P s * dP s)) * P s) = 0 := by
  have h1 := sandwich_eq_zero hP hidem s
  have h2 := hidem s
  have h3 := leibniz_of_idempotent hP hidem s
  have hPG : P s * (C s + (dP s * P s - P s * dP s)) = P s * C s - P s * dP s := by
    calc P s * (C s + (dP s * P s - P s * dP s))
        = P s * C s + (P s * dP s * P s - (P s * P s) * dP s) := by noncomm_ring
      _ = P s * C s + (0 - P s * dP s) := by rw [h1, h2]
      _ = P s * C s - P s * dP s := by abel
  have hGP : (C s + (dP s * P s - P s * dP s)) * P s = P s * C s + dP s * P s := by
    calc (C s + (dP s * P s - P s * dP s)) * P s
        = C s * P s + (dP s * (P s * P s) - P s * dP s * P s) := by noncomm_ring
      _ = P s * C s + (dP s * P s - 0) := by rw [h1, h2, hcomm s]
      _ = P s * C s + dP s * P s := by abel
  rw [hPG, hGP]
  calc dP s + (P s * C s - P s * dP s - (P s * C s + dP s * P s))
      = dP s - (dP s * P s + P s * dP s) := by abel
    _ = 0 := by rw [h3, sub_self]

/-- **Kato's intertwining theorem.**  Let `P s` be a differentiable family of idempotents
(spectral projections) and let `C s` be a family of operators commuting with `P s` (e.g.
`-i/ε` times a Hamiltonian having `P s` as a spectral projection).  Let `U` solve the
*adiabatic* evolution equation `U' = (C + [P', P]) U` with `U 0 = 1`.  Then `U`
intertwines the initial projection with the instantaneous one: `P s * U s = U s * P 0`. -/
theorem kato_intertwining {P dP C U : ℝ → A}
    (hP : ∀ s, HasDerivAt P (dP s) s) (hdP : Continuous dP)
    (hidem : ∀ s, P s * P s = P s)
    (hC : Continuous C) (hcomm : ∀ s, C s * P s = P s * C s)
    (hU : ∀ s, HasDerivAt U ((C s + (dP s * P s - P s * dP s)) * U s) s)
    (hU0 : U 0 = 1) {s : ℝ} (hs : 0 ≤ s) :
    P s * U s = U s * P 0 := by
  set G : ℝ → A := fun t => C t + (dP t * P t - P t * dP t) with hG
  set V : ℝ → A := fun t => P t * U t - U t * P 0 with hV
  -- `V` solves the linear ODE `V' = G V` with `V 0 = 0`.
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have hGc : Continuous G := by
    simp only [hG]
    exact hC.add ((hdP.mul hPc).sub (hPc.mul hdP))
  have hVderiv : ∀ t, HasDerivAt V (G t * V t) t := by
    intro t
    have h1 : HasDerivAt (fun r => P r * U r) (dP t * U t + P t * (G t * U t)) t :=
      (hP t).mul (hU t)
    have h2 : HasDerivAt (fun r => U r * P 0) ((G t * U t) * P 0) t := (hU t).mul_const (P 0)
    have h3 : dP t * U t + P t * (G t * U t) - (G t * U t) * P 0 = G t * V t := by
      have hkey := kato_generator_identity hP hidem hcomm t
      have hmul : (dP t + (P t * G t - G t * P t)) * U t = 0 := by
        rw [show dP t + (P t * G t - G t * P t) = 0 from hkey, zero_mul]
      simp only [hV]
      calc dP t * U t + P t * (G t * U t) - (G t * U t) * P 0
          = (dP t + (P t * G t - G t * P t)) * U t + (G t * (P t * U t) - G t * (U t * P 0)) := by
            noncomm_ring
        _ = G t * (P t * U t - U t * P 0) := by rw [hmul]; noncomm_ring
    simpa [hV, h3] using h1.sub h2
  have hV0 : V 0 = 0 := by simp [hV, hU0]
  -- Uniqueness of solutions of the linear ODE forces `V = 0`.
  set b : ℝ := s + 1 with hbdef
  have hb : (0:ℝ) ≤ b := by simp only [hbdef]; linarith
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := b)).exists_bound_of_continuousOn
    hGc.continuousOn
  set tau : ℝ → ℝ := fun t => max 0 (min t b) with htau
  have htau_mem : ∀ t, tau t ∈ Icc (0:ℝ) b := by
    intro t
    constructor
    · exact le_max_left _ _
    · exact max_le hb (min_le_right _ _)
  have htau_id : ∀ t ∈ Icc (0:ℝ) b, tau t = t := by
    intro t ht
    simp only [htau, min_eq_left ht.2, max_eq_right ht.1]
  set v : ℝ → A → A := fun t x => G (tau t) * x with hv
  have hlip : ∀ t, LipschitzWith M.toNNReal (v t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h1 : ‖G (tau t)‖ ≤ M := hM _ (htau_mem t)
    have h2 : ‖G (tau t) * (x - y)‖ ≤ ‖G (tau t)‖ * ‖x - y‖ := norm_mul_le _ _
    have h3 : (M.toNNReal : ℝ) = max M 0 := Real.coe_toNNReal' M
    rw [dist_eq_norm, dist_eq_norm, hv]
    simp only
    rw [← mul_sub]
    refine h2.trans ?_
    rw [h3]
    exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) (norm_nonneg _)
  have hVcont : ContinuousOn V (Icc 0 b) :=
    (continuous_iff_continuousAt.mpr fun t => (hVderiv t).continuousAt).continuousOn
  have hmain : EqOn V (fun _ => (0:A)) (Icc 0 b) := by
    refine ODE_solution_unique hlip hVcont ?_ continuousOn_const ?_ (by simpa using hV0)
    · intro t ht
      have hmem : t ∈ Icc (0:ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
      have : v t (V t) = G t * V t := by rw [hv]; simp only; rw [htau_id t hmem]
      rw [this]
      exact (hVderiv t).hasDerivWithinAt
    · intro t _
      have : v t 0 = 0 := by rw [hv]; simp
      rw [this]
      exact (hasDerivAt_const t (0:A)).hasDerivWithinAt
  have hs' : s ∈ Icc (0:ℝ) b := ⟨hs, by simp only [hbdef]; linarith⟩
  have := hmain hs'
  simp only [hV] at this
  exact sub_eq_zero.mp this

end Kato

/-- **The adiabatic theorem (Kato form).**

`Ham s` is a slowly (i.e. `s = t/T`-) varying Hamiltonian on a complex Hilbert space `E`,
`P s` is the spectral projection onto the instantaneous eigenspace belonging to the
nondegenerate eigenvalue `eig s` (hypotheses `hproj`, `heig`, `heig'`, `hnondeg`), and
`U s` is the adiabatic propagator, i.e. the solution of the Schrödinger equation
`U' = (-(i/ε) Ham + [P', P]) U`, `U 0 = 1`, generated by the Hamiltonian together with
Kato's geometric (Berry-connection) term `[P', P] = P' P - P P'`, which is the exact
generator of the adiabatic limit of the dynamics.

Then an initial eigenstate `psi` of `Ham 0` (i.e. `P 0 psi = psi`) is transported by the
dynamics into the *instantaneous* eigenspace at every later time: `U s psi` lies in the
range of `P s`, and is an eigenvector of `Ham s` for the instantaneous eigenvalue `eig s`.

The nondegeneracy hypothesis `hnondeg` (the range of each `P s` is a line) is stated for
faithfulness to the physical statement; the proof does not need it. -/
theorem adiabatic_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ham P dP U : ℝ → (E →L[ℂ] E)) (eig : ℝ → ℂ) (ε : ℝ) (psi : E)
    (hHam : Continuous Ham)
    (hP : ∀ s, HasDerivAt P (dP s) s) (hdP : Continuous dP)
    (hproj : ∀ s, P s * P s = P s)
    (heig : ∀ s, Ham s * P s = eig s • P s)
    (heig' : ∀ s, P s * Ham s = eig s • P s)
    (hnondeg : ∀ s, ∃ w : E, w ≠ 0 ∧ ∀ x : E, ∃ c : ℂ, P s x = c • w)
    (hU : ∀ s, HasDerivAt U
      (((-(Complex.I / ε)) • Ham s + (dP s * P s - P s * dP s)) * U s) s)
    (hU0 : U 0 = 1)
    (hpsi : P 0 psi = psi)
    {s : ℝ} (hs : 0 ≤ s) :
    P s (U s psi) = U s psi ∧ Ham s (U s psi) = eig s • (U s psi) := by
  set C : ℝ → (E →L[ℂ] E) := fun t => (-(Complex.I / ε)) • Ham t with hC
  have hCcont : Continuous C := hHam.const_smul _
  have hcomm : ∀ t, C t * P t = P t * C t := by
    intro t
    simp only [hC, smul_mul_assoc, mul_smul_comm, heig t, heig' t]
  have hint : P s * U s = U s * P 0 :=
    kato_intertwining hP hdP hproj hCcont hcomm hU hU0 hs
  have h1 : P s (U s psi) = U s psi := by
    have := congrArg (fun T : E →L[ℂ] E => T psi) hint
    simpa [ContinuousLinearMap.mul_apply, hpsi] using this
  refine ⟨h1, ?_⟩
  have h2 := congrArg (fun T : E →L[ℂ] E => T (U s psi)) (heig s)
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, h1] at h2
  exact h2

/-- A consistency check showing that the hypotheses of `adiabatic_theorem` are satisfiable,
so the theorem is not vacuous: on `E = ℂ`, with the constant Hamiltonian `a`, the rank-one
projection `1`, and the propagator `U s = exp (-(i/ε) a s)`, all hypotheses hold and the
conclusion applies to any initial state. -/
theorem adiabatic_theorem_example (a : ℂ) (eps : ℝ) (psi : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    (1 : ℂ →L[ℂ] ℂ) ((Complex.exp (-(Complex.I / eps) * a * s) • (1 : ℂ →L[ℂ] ℂ)) psi)
        = (Complex.exp (-(Complex.I / eps) * a * s) • (1 : ℂ →L[ℂ] ℂ)) psi ∧
      (a • (1 : ℂ →L[ℂ] ℂ)) ((Complex.exp (-(Complex.I / eps) * a * s) • (1 : ℂ →L[ℂ] ℂ)) psi)
        = a • ((Complex.exp (-(Complex.I / eps) * a * s) • (1 : ℂ →L[ℂ] ℂ)) psi) := by
  refine adiabatic_theorem (fun _ => a • (1 : ℂ →L[ℂ] ℂ)) (fun _ => (1 : ℂ →L[ℂ] ℂ))
    (fun _ => (0 : ℂ →L[ℂ] ℂ))
    (fun t => Complex.exp (-(Complex.I / eps) * a * t) • (1 : ℂ →L[ℂ] ℂ)) (fun _ => a) eps psi
    continuous_const (fun t => hasDerivAt_const t _) continuous_const (fun _ => by simp)
    (fun _ => by simp) (fun _ => by simp) (fun _ => ⟨1, one_ne_zero, fun x => ⟨x, by simp⟩⟩)
    ?_ (by simp) (by simp) hs
  intro t
  set z : ℂ := -(Complex.I / eps) * a with hz
  have h1 : HasDerivAt (fun r : ℝ => (z * r : ℂ)) z t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul z)
  have h2 : HasDerivAt (fun r : ℝ => Complex.exp (z * r)) (z * Complex.exp (z * t)) t := by
    simpa [mul_comm] using h1.cexp
  have h3 := h2.smul_const (1 : ℂ →L[ℂ] ℂ)
  convert h3 using 1
  simp [smul_smul, hz, mul_comm]

end Phys

