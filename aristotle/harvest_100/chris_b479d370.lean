/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option grind.warning false

namespace QI

open MeasureTheory MeasureTheory.Measure Complex

noncomputable section

/-! ## The quantum input: the Pusey–Barrett–Rudolph measurement on two qubits -/

/-- The real number `1/√2`, viewed as a complex amplitude. -/
noncomputable def rt : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma rt_mul_rt : rt * rt = 1 / 2 := by
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at h2
    norm_num at h2
  simp only [rt, Complex.ofReal_inv]
  field_simp
  linear_combination -h2

lemma conj_rt : (starRingEnd ℂ) rt = rt := by
  simp [rt]

lemma norm_rt_sq : ‖rt‖ ^ 2 = 1 / 2 := by
  simp [rt, Complex.norm_real, ← Real.sqrt_inv]

/-- The two single–qubit preparations used in the PBR argument:
`amp 0 = |0⟩ = (1, 0)` and `amp 1 = |+⟩ = (1/√2, 1/√2)`. -/
noncomputable def amp : Fin 2 → Fin 2 → ℂ := ![![1, 0], ![rt, rt]]

/-- Left tensor index of a basis vector of `ℂ⁴ = ℂ² ⊗ ℂ²`. -/
def idxL : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- Right tensor index of a basis vector of `ℂ⁴ = ℂ² ⊗ ℂ²`. -/
def idxR : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- The product state `|ψ_a⟩ ⊗ |ψ_b⟩` of two qubits, as a vector of `ℂ⁴`. -/
noncomputable def prodState (a b : Fin 2) : EuclideanSpace ℂ (Fin 4) :=
  (WithLp.toLp 2) fun i => amp a (idxL i) * amp b (idxR i)

/-- The four vectors of the entangled PBR measurement basis of `ℂ⁴`:
`(|01⟩+|10⟩)/√2`, `(|0-⟩+|1+⟩)/√2`, `(|+1⟩+|-0⟩)/√2`, `(|+-⟩+|-+⟩)/√2`. -/
noncomputable def pbrVec : Fin 4 → EuclideanSpace ℂ (Fin 4) :=
  ![!₂[0, rt, rt, 0],
    !₂[1 / 2, -(1 / 2), 1 / 2, 1 / 2],
    !₂[1 / 2, 1 / 2, -(1 / 2), 1 / 2],
    !₂[rt, 0, 0, -rt]]

/-- Index of the PBR outcome that has zero Born probability on the preparation
`|ψ_a⟩ ⊗ |ψ_b⟩`. -/
def pairIdx : Fin 2 → Fin 2 → Fin 4 := ![![0, 1], ![2, 3]]

/-- The PBR measurement is a genuine projective measurement: its four vectors are orthonormal,
hence an orthonormal basis of `ℂ⁴`. -/
lemma pbrVec_orthonormal : Orthonormal ℂ pbrVec := by
  constructor
  · intro i
    fin_cases i <;>
      · simp only [pbrVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
        rw [EuclideanSpace.norm_eq]
        simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, norm_rt_sq, norm_zero,
          norm_neg]
        norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [pbrVec, PiLp.inner_apply, Fin.sum_univ_four, conj_rt, rt_mul_rt]

/-- Each of the four product preparations is a unit vector. -/
lemma prodState_norm (a b : Fin 2) : ‖prodState a b‖ = 1 := by
  fin_cases a <;> fin_cases b <;>
    · rw [EuclideanSpace.norm_eq]
      simp only [prodState, amp, idxL, idxR, Fin.sum_univ_four, WithLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.tail_cons, Matrix.cons_val_fin_one]
      norm_num [norm_rt_sq, mul_pow]

/-- The key quantum fact behind the PBR theorem: outcome `pairIdx a b` of the PBR measurement
has zero amplitude, hence zero Born probability, on the product preparation `|ψ_a⟩ ⊗ |ψ_b⟩`. -/
lemma pbr_inner_eq_zero (a b : Fin 2) :
    inner ℂ (pbrVec (pairIdx a b)) (prodState a b) = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pairIdx, pbrVec, prodState, amp, idxL, idxR, PiLp.inner_apply, Fin.sum_univ_four,
      conj_rt, rt_mul_rt]

/-! ## A measure-theoretic tool: monotonicity of product measures -/

/-- If `μ ≤ μ'` and `ν ≤ ν'` then `μ ⊗ ν ≤ μ' ⊗ ν'`. -/
lemma prod_le_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ μ' : Measure α} {ν ν' : Measure β} [SFinite ν] [SFinite ν']
    (hμ : μ ≤ μ') (hν : ν ≤ ν') : μ.prod ν ≤ μ'.prod ν' := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.prod_apply hs, Measure.prod_apply hs]
  calc ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ ≤ ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ :=
        lintegral_mono fun _ => Measure.le_iff'.mp hν _
    _ ≤ ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ' := lintegral_mono' hμ le_rfl

/-! ## The PBR theorem -/

/-- **Pusey–Barrett–Rudolph theorem.**

Consider an ontological (hidden-variable) model on a measurable space `Λ` of ontic states, in
which the two qubit preparations `|ψ₀⟩ = |0⟩` and `|ψ₁⟩ = |+⟩` are represented by probability
measures `μ 0` and `μ 1` on `Λ`.  Assume:

* *preparation independence*: the ontic state of two independently prepared systems is
  distributed according to the product measure `(μ a).prod (μ b)`;
* the model reproduces the Born rule for the entangled PBR measurement `pbrVec` on the two-qubit
  system: measurable response functions `ξ k : Λ × Λ → ℝ≥0∞` with `∑ k, ξ k x = 1` for every
  ontic state `x`, whose averages against the prepared distribution give the Born probabilities
  `|⟨pbrVec k, ψ_a ⊗ ψ_b⟩|²`.

Then the two quantum states are *ontologically distinct*: the measures `μ 0` and `μ 1` are
mutually singular, so no ontic state is compatible with both preparations.  In other words, the
quantum state is an ontic (physical) property of the system, not a merely epistemic one. -/
theorem pbr_theorem {Λ : Type*} [MeasurableSpace Λ] (μ : Fin 2 → Measure Λ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (ξ : Fin 4 → Λ × Λ → ENNReal)
    (hmeas : ∀ k, Measurable (ξ k))
    (hsum : ∀ x, ∑ k, ξ k x = 1)
    (hBorn : ∀ (a b : Fin 2) (k : Fin 4),
      ∫⁻ x, ξ k x ∂((μ a).prod (μ b))
        = ENNReal.ofReal (‖inner ℂ (pbrVec k) (prodState a b)‖ ^ 2)) :
    μ 0 ⟂ₘ μ 1 := by
  rw [Measure.mutuallySingular_iff_disjoint]
  intro ν h0 h1
  haveI : IsFiniteMeasure ν := isFiniteMeasure_of_le (μ 0) h0
  have hle : ∀ a : Fin 2, ν ≤ μ a := by
    intro a
    fin_cases a
    · exact h0
    · exact h1
  -- Every PBR outcome has vanishing probability under the overlap measure `ν ⊗ ν`.
  have hzero : ∀ k : Fin 4, ∫⁻ x, ξ k x ∂(ν.prod ν) = 0 := by
    intro k
    obtain ⟨a, b, hk⟩ : ∃ a b : Fin 2, k = pairIdx a b := by
      fin_cases k
      exacts [⟨0, 0, rfl⟩, ⟨0, 1, rfl⟩, ⟨1, 0, rfl⟩, ⟨1, 1, rfl⟩]
    have hprod : ν.prod ν ≤ (μ a).prod (μ b) := prod_le_prod (hle a) (hle b)
    have hmono : ∫⁻ x, ξ k x ∂(ν.prod ν) ≤ ∫⁻ x, ξ k x ∂((μ a).prod (μ b)) :=
      lintegral_mono' hprod le_rfl
    rw [hBorn a b k, hk, pbr_inner_eq_zero] at hmono
    simpa using hmono
  -- Hence the total mass of `ν ⊗ ν` vanishes.
  have htotal : (ν.prod ν) Set.univ = 0 := by
    have hone : ∫⁻ _, (1 : ENNReal) ∂(ν.prod ν) = 0 := by
      calc ∫⁻ _, (1 : ENNReal) ∂(ν.prod ν) = ∫⁻ x, ∑ k, ξ k x ∂(ν.prod ν) := by
            refine lintegral_congr fun x => ?_
            rw [hsum x]
        _ = ∑ k, ∫⁻ x, ξ k x ∂(ν.prod ν) :=
            lintegral_finset_sum _ fun k _ => hmeas k
        _ = 0 := by simp [hzero]
    simpa using hone
  have hν : ν Set.univ = 0 := by
    have : ν Set.univ * ν Set.univ = 0 := by
      rw [← Set.univ_prod_univ, Measure.prod_prod] at htotal
      exact htotal
    rcases mul_eq_zero.mp this with h | h <;> exact h
  simpa using (Measure.measure_univ_eq_zero.mp hν)

end

end QI

