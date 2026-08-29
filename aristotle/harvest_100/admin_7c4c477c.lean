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

open MeasureTheory

noncomputable section

namespace QI

/-! ## The quantum ingredients

We work with a single qubit modelled as `Fin 2 → ℂ` and a pair of qubits modelled as
`Fin 2 × Fin 2 → ℂ` (the tensor product `ℂ² ⊗ ℂ²`), equipped with the standard Hermitian
inner product `inner2`.
-/

/-- The scalar `1/√2`. -/
def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrtTwo_mul : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  unfold invSqrtTwo
  field_simp
  linear_combination -h2

lemma invSqrtTwo_sq : invSqrtTwo ^ 2 = 1 / 2 := by rw [pow_two, invSqrtTwo_mul]

lemma invSqrtTwo_pow4 : invSqrtTwo ^ 4 = 1 / 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, invSqrtTwo_sq]; norm_num

lemma invSqrtTwo_pow6 : invSqrtTwo ^ 6 = 1 / 8 := by
  have h : invSqrtTwo ^ 6 = (invSqrtTwo ^ 2) ^ 3 := by ring
  rw [h, invSqrtTwo_sq]; norm_num

lemma conj_invSqrtTwo : (starRingEnd ℂ) invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo, ← Complex.ofReal_inv, Complex.conj_ofReal]

/-- The computational basis state `|0⟩`. -/
def ket0 : Fin 2 → ℂ := ![1, 0]

/-- The computational basis state `|1⟩`. -/
def ket1 : Fin 2 → ℂ := ![0, 1]

/-- The state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
def ketPlus : Fin 2 → ℂ := ![invSqrtTwo, invSqrtTwo]

/-- The state `|-⟩ = (|0⟩ - |1⟩)/√2`. -/
def ketMinus : Fin 2 → ℂ := ![invSqrtTwo, -invSqrtTwo]

/-- The tensor product of two single-qubit vectors. -/
def tensor (u v : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun p => u p.1 * v p.2

/-- The two nonorthogonal preparations used by Pusey–Barrett–Rudolph: `|0⟩` and `|+⟩`. -/
def qstate : Fin 2 → (Fin 2 → ℂ) := ![ket0, ketPlus]

/-- The standard Hermitian inner product on `ℂ² ⊗ ℂ²`. -/
def inner2 (u v : Fin 2 × Fin 2 → ℂ) : ℂ := ∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (u p) * v p

/-- The four vectors of the PBR entangled measurement basis, indexed by the pair of
preparation choices `(x₁, x₂)` that the corresponding outcome excludes. -/
def pbrVec : Fin 2 × Fin 2 → (Fin 2 × Fin 2 → ℂ) := fun k =>
  match k.1, k.2 with
  | 0, 0 => fun p => invSqrtTwo * (tensor ket0 ket1 p + tensor ket1 ket0 p)
  | 0, 1 => fun p => invSqrtTwo * (tensor ket0 ketMinus p + tensor ket1 ketPlus p)
  | 1, 0 => fun p => invSqrtTwo * (tensor ketPlus ket1 p + tensor ketMinus ket0 p)
  | 1, 1 => fun p => invSqrtTwo * (tensor ketPlus ketMinus p + tensor ketMinus ketPlus p)

lemma inner2_eq (u v : Fin 2 × Fin 2 → ℂ) :
    inner2 u v = (starRingEnd ℂ) (u (0, 0)) * v (0, 0) + (starRingEnd ℂ) (u (0, 1)) * v (0, 1)
      + (starRingEnd ℂ) (u (1, 0)) * v (1, 0) + (starRingEnd ℂ) (u (1, 1)) * v (1, 1) := by
  simp [inner2, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

/-- The PBR vectors form an orthonormal basis of `ℂ² ⊗ ℂ²`, i.e. they really do describe a
projective measurement on the two-qubit system. -/
theorem pbr_orthonormal (j k : Fin 2 × Fin 2) :
    inner2 (pbrVec j) (pbrVec k) = if j = k then 1 else 0 := by
  obtain ⟨j1, j2⟩ := j
  obtain ⟨k1, k2⟩ := k
  fin_cases j1 <;> fin_cases j2 <;> fin_cases k1 <;> fin_cases k2 <;>
    simp [inner2_eq, pbrVec, tensor, ket0, ket1, ketPlus, ketMinus, conj_invSqrtTwo,
      Prod.ext_iff] <;>
    ring_nf <;>
    try (simp [invSqrtTwo_sq, invSqrtTwo_pow4, invSqrtTwo_pow6]; try ring_nf)

/-- The key quantum fact behind PBR: for each of the four product preparations
`|ψ_{x₁}⟩ ⊗ |ψ_{x₂}⟩` (with `ψ₀ = |0⟩`, `ψ₁ = |+⟩`) the outcome labelled by `(x₁, x₂)` has
Born probability zero. -/
theorem pbr_orthogonal_to_prep (x : Fin 2 × Fin 2) :
    inner2 (pbrVec x) (tensor (qstate x.1) (qstate x.2)) = 0 := by
  obtain ⟨x1, x2⟩ := x
  fin_cases x1 <;> fin_cases x2 <;>
    (simp [inner2_eq, pbrVec, tensor, qstate, ket0, ket1, ketPlus, ketMinus, conj_invSqrtTwo]
      <;> try ring)

/-! ## Measure-theoretic preliminaries -/

/-- Monotonicity of the product of measures. -/
lemma prod_le_prod_of_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ₁ μ₂ : Measure α} {ν₁ ν₂ : Measure β} [SFinite ν₁] [SFinite ν₂]
    (h : μ₁ ≤ μ₂) (h' : ν₁ ≤ ν₂) : μ₁.prod ν₁ ≤ μ₂.prod ν₂ := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.prod_apply hs, Measure.prod_apply hs]
  exact lintegral_mono' h fun x => h' _

/-! ## The PBR theorem

An *ontological model* for the two preparations `|0⟩` and `|+⟩` consists of a measurable space
`Λ` of ontic states together with a probability measure `μ i` for each preparation.  A
measurement on two systems is modelled by response functions `ξ k : Λ × Λ → ℝ≥0∞`, one for each
outcome `k`, summing pointwise to `1`.  *Preparation independence* is the statement that the
ontic state of two independently prepared systems is distributed according to the **product**
measure `(μ x₁).prod (μ x₂)`; this is exactly how the Born-rule hypothesis below is phrased.

The theorem states that under these assumptions the two distributions `μ 0` and `μ 1` have no
common part whatsoever: any measure `ρ` below both of them is zero.  In other words, the ontic
state determines the quantum state — the quantum state is ontic, not epistemic.
-/

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model of the qubit preparations
`|0⟩` and `|+⟩` that reproduces the Born rule for the PBR entangled measurement on two systems
and satisfies preparation independence (the joint ontic distribution of two independently
prepared systems is the product of the single-system distributions), the ontic distributions of
`|0⟩` and `|+⟩` have no overlap: every measure `ρ` dominated by both of them vanishes.  Hence no
`ψ`-epistemic model is possible: the quantum state is ontic. -/
theorem pbr_theorem
    {Λ : Type*} [MeasurableSpace Λ]
    (μ : Fin 2 → Measure Λ) [hp : ∀ i, IsProbabilityMeasure (μ i)]
    (ξ : Fin 2 × Fin 2 → Λ × Λ → ENNReal)
    (hmeas : ∀ k, Measurable (ξ k))
    (hnorm : ∀ l, ∑ k : Fin 2 × Fin 2, ξ k l = 1)
    (hBorn : ∀ k x : Fin 2 × Fin 2,
      ∫⁻ l, ξ k l ∂((μ x.1).prod (μ x.2))
        = ENNReal.ofReal (‖inner2 (pbrVec k) (tensor (qstate x.1) (qstate x.2))‖ ^ 2))
    (ρ : Measure Λ) (h0 : ρ ≤ μ 0) (h1 : ρ ≤ μ 1) :
    ρ = 0 := by
  -- `ρ` is a finite measure, hence s-finite, so products with it are well behaved.
  have hfin : IsFiniteMeasure ρ := by
    refine ⟨lt_of_le_of_lt (h0 Set.univ) ?_⟩
    rw [(hp 0).measure_univ]
    exact ENNReal.one_lt_top
  have hμle : ∀ i : Fin 2, ρ ≤ μ i := by
    intro i; fin_cases i
    · exact h0
    · exact h1
  -- For each preparation pair `x`, the outcome `x` never occurs.
  have hzero : ∀ x : Fin 2 × Fin 2, ((μ x.1).prod (μ x.2)) {l | ξ x l ≠ 0} = 0 := by
    intro x
    have hint : ∫⁻ l, ξ x l ∂((μ x.1).prod (μ x.2)) = 0 := by
      rw [hBorn x x, pbr_orthogonal_to_prep x]
      simp
    have := (lintegral_eq_zero_iff (hmeas x)).1 hint
    have h' : ∀ᵐ l ∂((μ x.1).prod (μ x.2)), ξ x l = 0 := this
    rwa [ae_iff] at h'
  -- Hence the same holds for the product of `ρ` with itself.
  have hzero' : ∀ x : Fin 2 × Fin 2, (ρ.prod ρ) {l | ξ x l ≠ 0} = 0 := by
    intro x
    refine le_antisymm ?_ (zero_le _)
    calc (ρ.prod ρ) {l | ξ x l ≠ 0}
        ≤ ((μ x.1).prod (μ x.2)) {l | ξ x l ≠ 0} :=
          prod_le_prod_of_le (hμle x.1) (hμle x.2) _
      _ = 0 := hzero x
  -- But some outcome must occur, so `ρ.prod ρ` is the zero measure.
  have huniv : (ρ.prod ρ) Set.univ = 0 := by
    have hsub : (Set.univ : Set (Λ × Λ)) ⊆ ⋃ x : Fin 2 × Fin 2, {l | ξ x l ≠ 0} := by
      intro l _
      by_contra hl
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hl
      have := hnorm l
      rw [Finset.sum_congr rfl fun x _ => hl x] at this
      simp at this
    refine le_antisymm ?_ (zero_le _)
    calc (ρ.prod ρ) Set.univ
        ≤ (ρ.prod ρ) (⋃ x : Fin 2 × Fin 2, {l | ξ x l ≠ 0}) := measure_mono hsub
      _ = 0 := measure_iUnion_null fun x => hzero' x
  -- Therefore `ρ` itself vanishes.
  have : ρ Set.univ * ρ Set.univ = 0 := by
    rw [← Measure.prod_prod (μ := ρ) (ν := ρ) Set.univ Set.univ, Set.univ_prod_univ]
    exact huniv
  rcases mul_eq_zero.1 this with h | h <;>
    exact Measure.measure_univ_eq_zero.1 h

end QI

