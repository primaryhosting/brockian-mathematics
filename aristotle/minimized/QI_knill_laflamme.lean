/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the required header is
-- repeated verbatim as the module docstring immediately below the import.)

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
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

open Matrix ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- The **Knill–Laflamme conditions** for a code with orthogonal projector `P` and a set of
error operators `E i`: `P (E i)ᴴ (E j) P = c i j • P` for some matrix of scalars `c`. -/
def KLConditions (P : Matrix d d ℂ) (E : ι → Matrix d d ℂ) : Prop :=
  ∃ c : ι → ι → ℂ, ∀ i j, P * (E i)ᴴ * E j * P = c i j • P

/-- The code with orthogonal projector `P` **corrects** the error set `E` if there is a
recovery channel, given by Kraus operators `R k` with `∑ k, (R k)ᴴ * (R k) = 1`, which
undoes the error channel `ρ ↦ ∑ i, E i * ρ * (E i)ᴴ` on all states supported on the code. -/
def Correctable (P : Matrix d d ℂ) (E : ι → Matrix d d ℂ) : Prop :=
  ∃ (m : ℕ) (R : Fin m → Matrix d d ℂ),
    (∑ k, (R k)ᴴ * R k = 1) ∧
    ∀ ρ : Matrix d d ℂ, P * ρ * P = ρ →
      (∑ k, ∑ i, (R k * E i) * ρ * (R k * E i)ᴴ) = ρ

/-! ## Elementary lemmas -/

omit [Fintype d] [DecidableEq d] in
lemma smul_proj_inj {P : Matrix d d ℂ} (hP0 : P ≠ 0) {a b : ℂ} (h : a • P = b • P) : a = b := by
  have h2 : (a - b) • P = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hP0

omit [DecidableEq d] in
lemma conj_mul_outer (M : Matrix d d ℂ) (v : d → ℂ) :
    M * vecMulVec v (star v) * Mᴴ = vecMulVec (M *ᵥ v) (star (M *ᵥ v)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, star_mulVec]

omit [DecidableEq d] in
lemma outer_quadratic (v w : d → ℂ) :
    star w ⬝ᵥ (vecMulVec v (star v) *ᵥ w) = star (star w ⬝ᵥ v) * (star w ⬝ᵥ v) := by
  simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    Finset.mul_sum, Finset.sum_mul, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq d] in
lemma exists_mulVec_ne_zero {P : Matrix d d ℂ} (hP0 : P ≠ 0) : ∃ v : d → ℂ, P *ᵥ v ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hP0 (ext_iff_mulVec.mpr fun v => by simp [hc v])

omit [DecidableEq d] in
lemma dotProduct_star_self_ofReal (v : d → ℂ) :
    star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, RCLike.star_def, mul_comm, Complex.mul_conj]
  norm_cast
  exact (Complex.normSq_eq_norm_sq (v i)) ▸ rfl

/-! ## Correctable implies the Knill–Laflamme conditions -/

omit [DecidableEq d] in
/-- If a sum of positive terms `M k ψψᴴ (M k)ᴴ` equals the rank-one projector `ψψᴴ`, then each
`M k` maps `ψ` to a multiple of itself. -/
lemma exists_smul_of_sum_outer {κ : Type*} [Fintype κ] (M : κ → Matrix d d ℂ)
    (ψ : d → ℂ) (hψ : ψ ≠ 0)
    (h : ∑ k, M k * vecMulVec ψ (star ψ) * (M k)ᴴ = vecMulVec ψ (star ψ)) (k : κ) :
    ∃ t : ℂ, M k *ᵥ ψ = t • ψ := by
  have hnψ : star ψ ⬝ᵥ ψ ≠ 0 := fun h0 => hψ (dotProduct_star_self_eq_zero.mp h0)
  refine ⟨(star ψ ⬝ᵥ (M k *ᵥ ψ)) / (star ψ ⬝ᵥ ψ), ?_⟩
  set t : ℂ := (star ψ ⬝ᵥ (M k *ᵥ ψ)) / (star ψ ⬝ᵥ ψ) with ht
  set w0 : d → ℂ := M k *ᵥ ψ - t • ψ with hw0def
  have hw0ψ : star ψ ⬝ᵥ w0 = 0 := by
    rw [hw0def, dotProduct_sub, dotProduct_smul, smul_eq_mul, ht]
    field_simp
    ring
  have hψw0 : star w0 ⬝ᵥ ψ = 0 := by
    rw [star_dotProduct, hw0ψ]; simp
  have key : ∀ l, star w0 ⬝ᵥ (M l *ᵥ ψ) = 0 := by
    have h1 : star w0 ⬝ᵥ ((∑ l, M l * vecMulVec ψ (star ψ) * (M l)ᴴ) *ᵥ w0)
        = star w0 ⬝ᵥ (vecMulVec ψ (star ψ) *ᵥ w0) := by rw [h]
    rw [Matrix.sum_mulVec, dotProduct_sum, outer_quadratic, hψw0] at h1
    simp only [conj_mul_outer, outer_quadratic, mul_zero] at h1
    have h2 : star (fun l => star w0 ⬝ᵥ (M l *ᵥ ψ)) ⬝ᵥ (fun l => star w0 ⬝ᵥ (M l *ᵥ ψ)) = 0 := by
      simpa [dotProduct] using h1
    exact fun l => congrFun (dotProduct_star_self_eq_zero.mp h2) l
  have hw00 : star w0 ⬝ᵥ w0 = 0 := by
    rw [hw0def, dotProduct_sub, dotProduct_smul, key k, hψw0, smul_zero, sub_zero]
  have h3 := dotProduct_star_self_eq_zero.mp hw00
  rw [hw0def] at h3
  exact sub_eq_zero.mp h3

omit [DecidableEq d] in
/-- An operator acting as a scalar on every vector of the code acts as a fixed scalar on the
whole code. -/
lemma exists_smul_proj {P : Matrix d d ℂ} (hPi : P * P = P) (hP0 : P ≠ 0)
    {M : Matrix d d ℂ} (h : ∀ ψ : d → ℂ, P *ᵥ ψ = ψ → ∃ t : ℂ, M *ᵥ ψ = t • ψ) :
    ∃ t : ℂ, M * P = t • P := by
  obtain ⟨v₀, hv₀⟩ := exists_mulVec_ne_zero hP0
  have hu₀ : P *ᵥ (P *ᵥ v₀) = P *ᵥ v₀ := by rw [mulVec_mulVec, hPi]
  obtain ⟨t₀, ht₀⟩ := h (P *ᵥ v₀) hu₀
  refine ⟨t₀, ext_iff_mulVec.mpr fun v => ?_⟩
  rw [← mulVec_mulVec, smul_mulVec]
  set u := P *ᵥ v with hudef
  have hu : P *ᵥ u = u := by rw [hudef, mulVec_mulVec, hPi]
  rcases eq_or_ne u 0 with h0 | h0
  · rw [h0]; simp
  obtain ⟨t, ht⟩ := h u hu
  suffices ht0 : t = t₀ by rw [ht, ht0]
  obtain ⟨s, hs⟩ := h (u + P *ᵥ v₀) (by rw [mulVec_add, hu, hu₀])
  rw [mulVec_add, ht, ht₀, smul_add] at hs
  have hkey : (t - s) • u = (s - t₀) • (P *ᵥ v₀) := by
    rw [sub_smul, sub_smul]
    linear_combination (norm := module) hs
  rcases eq_or_ne s t₀ with hst | hst
  · rw [hst, sub_self, zero_smul] at hkey
    rcases smul_eq_zero.mp hkey with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 h0
  · have hne : s - t₀ ≠ 0 := sub_ne_zero.mpr hst
    have hv0eq : P *ᵥ v₀ = ((t - s) / (s - t₀)) • u := by
      rw [div_eq_mul_inv, mul_comm, ← smul_smul, hkey, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have h1 : M *ᵥ (P *ᵥ v₀) = t • (P *ᵥ v₀) := by
      rw [hv0eq, mulVec_smul, ht, smul_smul, smul_smul, mul_comm]
    rw [ht₀] at h1
    have h4 := sub_eq_zero.mpr h1.symm
    rw [← sub_smul] at h4
    rcases smul_eq_zero.mp h4 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hv₀

omit [DecidableEq ι] in
theorem correctable_imp_klConditions {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ}
    (hPh : Pᴴ = P) (hPi : P * P = P) (hP0 : P ≠ 0) (h : Correctable P E) :
    KLConditions P E := by
  obtain ⟨m, R, hR1, hR2⟩ := h
  have hprop : ∀ (k : Fin m) (i : ι), ∃ t : ℂ, (R k * E i) * P = t • P := by
    intro k i
    refine exists_smul_proj hPi hP0 (fun ψ hψ => ?_)
    rcases eq_or_ne ψ 0 with rfl | hψ0
    · exact ⟨0, by simp⟩
    have hstar : star ψ ᵥ* P = star ψ := by
      conv_lhs => rw [← hPh, ← star_mulVec, hψ]
    have hρ : P * vecMulVec ψ (star ψ) * P = vecMulVec ψ (star ψ) := by
      rw [Matrix.mul_vecMulVec, hψ, Matrix.vecMulVec_mul, hstar]
    have hsum : ∑ p : Fin m × ι, (R p.1 * E p.2) * vecMulVec ψ (star ψ) * (R p.1 * E p.2)ᴴ
        = vecMulVec ψ (star ψ) := by
      rw [Fintype.sum_prod_type]
      exact hR2 _ hρ
    exact exists_smul_of_sum_outer (fun p : Fin m × ι => R p.1 * E p.2) ψ hψ0 hsum (k, i)
  choose lam hlam using hprop
  refine ⟨fun i j => ∑ k, star (lam k i) * lam k j, fun i j => ?_⟩
  have expand : P * (E i)ᴴ * E j * P = ∑ k, ((R k * E i) * P)ᴴ * ((R k * E j) * P) := by
    have h5 : P * (E i)ᴴ * E j * P = P * (E i)ᴴ * (∑ k, (R k)ᴴ * R k) * E j * P := by
      rw [hR1, Matrix.mul_one]
    rw [h5, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_mul, hPh, Matrix.mul_assoc]
  rw [expand, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hlam k i, hlam k j, conjTranspose_smul, hPh, smul_mul_assoc, Matrix.mul_smul, smul_smul, hPi]

/-! ## The Knill–Laflamme conditions imply correctability -/

omit [DecidableEq d] [Fintype ι] [DecidableEq ι] in
/-- On the code space, the Knill–Laflamme scalars compute the inner products of the erroneous
states. -/
lemma code_inner_apply {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ} {c : ι → ι → ℂ}
    (hPh : Pᴴ = P) (hKL : ∀ i j, P * (E i)ᴴ * E j * P = c i j • P)
    {u : d → ℂ} (hPu : P *ᵥ u = u) (i j : ι) :
    star (E i *ᵥ u) ⬝ᵥ (E j *ᵥ u) = c i j * (star u ⬝ᵥ u) := by
  have hstar : star u ᵥ* P = star u := by
    conv_lhs => rw [← hPh, ← star_mulVec, hPu]
  have step1 : star (E i *ᵥ u) ⬝ᵥ (E j *ᵥ u) = star u ⬝ᵥ (((E i)ᴴ * E j) *ᵥ u) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  have step2 : (P * (E i)ᴴ * E j * P) *ᵥ u = P *ᵥ (((E i)ᴴ * E j) *ᵥ u) := by
    rw [← mulVec_mulVec, hPu, Matrix.mul_assoc, ← mulVec_mulVec]
  have step3 : star u ⬝ᵥ (((E i)ᴴ * E j) *ᵥ u) = star u ⬝ᵥ ((P * (E i)ᴴ * E j * P) *ᵥ u) := by
    conv_rhs => rw [step2, dotProduct_mulVec, hstar]
  rw [step1, step3, hKL i j, smul_mulVec, dotProduct_smul, hPu, smul_eq_mul]

omit [DecidableEq d] [DecidableEq ι] in
/-- The matrix of Knill–Laflamme scalars is positive semidefinite. -/
lemma kl_posSemidef {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ} {c : ι → ι → ℂ}
    (hPh : Pᴴ = P) (hPi : P * P = P) (hP0 : P ≠ 0)
    (hKL : ∀ i j, P * (E i)ᴴ * E j * P = c i j • P) : (Matrix.of c).PosSemidef := by
  obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hP0
  set u := P *ᵥ v with hu
  have hPu : P *ᵥ u = u := by rw [hu, mulVec_mulVec, hPi]
  set r : ℝ := ∑ x, ‖u x‖ ^ 2 with hrdef
  have hr : 0 < r := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hv
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨x, Finset.mem_univ x, ?_⟩
    have hne : ‖u x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    positivity
  have hr0 : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hru : star u ⬝ᵥ u = (r : ℂ) := dotProduct_star_self_ofReal u
  have hsq : ((Real.sqrt r : ℂ))⁻¹ * ((Real.sqrt r : ℂ))⁻¹ = ((r : ℂ))⁻¹ := by
    rw [← mul_inv]
    norm_cast
    rw [Real.mul_self_sqrt hr.le]
  set A : Matrix d ι ℂ := Matrix.of fun x j => ((Real.sqrt r : ℂ))⁻¹ * (E j *ᵥ u) x with hA
  have hAA : Aᴴ * A = Matrix.of c := by
    ext i j
    simp only [Matrix.mul_apply, conjTranspose_apply, hA, Matrix.of_apply, RCLike.star_def,
      map_mul, map_inv₀, Complex.conj_ofReal]
    have hterm : ∀ x : d, ((Real.sqrt r : ℂ))⁻¹ * (starRingEnd ℂ) ((E i *ᵥ u) x) *
        (((Real.sqrt r : ℂ))⁻¹ * (E j *ᵥ u) x)
        = ((r : ℂ))⁻¹ * ((starRingEnd ℂ) ((E i *ᵥ u) x) * (E j *ᵥ u) x) := by
      intro x; rw [← hsq]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
    have hdp : ∑ x, (starRingEnd ℂ) ((E i *ᵥ u) x) * (E j *ᵥ u) x
        = star (E i *ᵥ u) ⬝ᵥ (E j *ᵥ u) := by
      simp [dotProduct]
    rw [hdp, code_inner_apply hPh hKL hPu i j, hru]
    field_simp
  rw [← hAA]
  exact posSemidef_conjTranspose_mul_self A

/-- Unitary diagonalization of a positive semidefinite matrix. -/
lemma exists_unitary_diagonalization {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    ∃ (U : Matrix ι ι ℂ) (dd : ι → ℝ), (∀ i, 0 ≤ dd i) ∧ Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * C * U = diagonal (fun i => (dd i : ℂ)) ∧ C.trace = ∑ i, (dd i : ℂ) := by
  have hspec0 : C = (hC.1.eigenvectorUnitary : Matrix ι ι ℂ) *
      (diagonal (fun i => (hC.1.eigenvalues i : ℂ))) *
      (hC.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hC.1.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hUsU0 : (hC.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
      (hC.1.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hC.1.eigenvectorUnitary
  have hUUs0 : (hC.1.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hC.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hC.1.eigenvectorUnitary
  have htr0 : C.trace = ∑ i, (hC.1.eigenvalues i : ℂ) := hC.1.trace_eq_sum_eigenvalues
  have hnn0 : ∀ i, 0 ≤ hC.1.eigenvalues i := hC.eigenvalues_nonneg
  revert hspec0 hUsU0 hUUs0 htr0 hnn0
  generalize (hC.1.eigenvectorUnitary : Matrix ι ι ℂ) = U
  generalize hC.1.eigenvalues = dd
  intro hspec hUsU hUUs htr hnn
  refine ⟨U, dd, hnn, hUsU, hUUs, ?_, htr⟩
  calc Uᴴ * C * U = (Uᴴ * U) * (diagonal (fun i => (dd i : ℂ))) * (Uᴴ * U) := by
        rw [hspec]; simp [Matrix.mul_assoc]
    _ = diagonal (fun i => (dd i : ℂ)) := by rw [hUsU]; simp

/-- A unitary change of the Kraus operators does not change the channel. -/
lemma sum_unitary_kraus (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) (E : ι → Matrix d d ℂ)
    (ρ : Matrix d d ℂ) :
    ∑ k, (∑ i, U i k • E i) * ρ * (∑ i, U i k • E i)ᴴ = ∑ i, E i * ρ * (E i)ᴴ := by
  have hexp : ∀ k : ι, (∑ i, U i k • E i) * ρ * (∑ i, U i k • E i)ᴴ
      = ∑ i, ∑ j, (U i k * star (U j k)) • (E i * ρ * (E j)ᴴ) := by
    intro k
    rw [conjTranspose_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_smul]
    simp [smul_smul, mul_comm]
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have hcol : ∀ j : ι, ∑ k, (U i k * star (U j k)) • (E i * ρ * (E j)ᴴ)
      = ((U * Uᴴ) i j) • (E i * ρ * (E j)ᴴ) := by
    intro j
    rw [← Finset.sum_smul]
    congr 1
  simp only [hcol, hU]
  simp [Matrix.one_apply]

omit [DecidableEq d] [DecidableEq ι] in
/-- The Knill–Laflamme conditions in a rotated Kraus basis. -/
lemma kl_conj_unitary {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ} {c : ι → ι → ℂ}
    (hKL : ∀ i j, P * (E i)ᴴ * E j * P = c i j • P) (U : Matrix ι ι ℂ) (k l : ι) :
    P * (∑ i, U i k • E i)ᴴ * (∑ j, U j l • E j) * P = ((Uᴴ * Matrix.of c * U) k l) • P := by
  have expand : P * (∑ i, U i k • E i)ᴴ * (∑ j, U j l • E j) * P
      = ∑ i, ∑ j, (star (U i k) * U j l) • (P * (E i)ᴴ * E j * P) := by
    simp only [conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Finset.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring_nf
  rw [expand]
  simp only [hKL, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Finset.sum_mul,
    RCLike.star_def]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq d] [DecidableEq ι] in
/-- Composing a channel with a single Kraus operator. -/
lemma sum_kraus_conj (X : Matrix d d ℂ) (E : ι → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    ∑ i, (X * E i) * ρ * (X * E i)ᴴ = X * (∑ i, E i * ρ * (E i)ᴴ) * Xᴴ := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_mul]
  simp [Matrix.mul_assoc]

omit [DecidableEq d] in
/-- Kraus operators may be restricted to the code space. -/
lemma kraus_restrict {P : Matrix d d ℂ} (hPh : Pᴴ = P) (X : Matrix d d ℂ) {ρ : Matrix d d ℂ}
    (hρ : P * ρ * P = ρ) : X * ρ * Xᴴ = (X * P) * ρ * (X * P)ᴴ := by
  have h1 : (X * P) * ρ * (X * P)ᴴ = X * (P * ρ * P) * Xᴴ := by
    rw [conjTranspose_mul, hPh]
    simp [Matrix.mul_assoc]
  rw [h1, hρ]

omit [DecidableEq d] in
/-- Conjugating by a real multiple of the projector. -/
lemma smul_real_proj_conj {P : Matrix d d ℂ} (hPh : Pᴴ = P) (t : ℝ) (ρ : Matrix d d ℂ) :
    ((t : ℂ) • P) * ρ * ((t : ℂ) • P)ᴴ = ((t * t : ℝ) : ℂ) • (P * ρ * P) := by
  rw [conjTranspose_smul, hPh]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def, Complex.conj_ofReal,
    Complex.ofReal_mul]

lemma real_inv_sqrt_mul_self {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x)⁻¹ * x = Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · simp [← h0]
  · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr h0
    field_simp
    exact (Real.sq_sqrt hx).symm

theorem klConditions_imp_correctable {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ}
    (hPh : Pᴴ = P) (hPi : P * P = P) (hP0 : P ≠ 0) (hE : ∑ i, (E i)ᴴ * E i = 1)
    (h : KLConditions P E) : Correctable P E := by
  obtain ⟨c, hKL⟩ := h
  obtain ⟨U, dd, hnn, hUsU, hUUs, hdiag, htr⟩ :=
    exists_unitary_diagonalization (kl_posSemidef hPh hPi hP0 hKL)
  obtain ⟨F, hF⟩ : ∃ F : ι → Matrix d d ℂ, F = fun k => ∑ i, U i k • E i := ⟨_, rfl⟩
  have hFKL : ∀ k l, P * (F k)ᴴ * F l * P = (if k = l then (dd k : ℂ) else 0) • P := by
    intro k l
    rw [hF, kl_conj_unitary hKL U k l, hdiag, Matrix.diagonal_apply]
  have hFchan : ∀ ρ, ∑ k, F k * ρ * (F k)ᴴ = ∑ i, E i * ρ * (E i)ᴴ := by
    intro ρ; rw [hF]; exact sum_unitary_kraus U hUUs E ρ
  have hcsum : ∑ i, c i i = 1 := by
    have e1 : ∑ i, (P * (E i)ᴴ * E i * P) = (∑ i, c i i) • P := by
      simp only [hKL, ← Finset.sum_smul]
    have e2 : ∑ i, (P * (E i)ᴴ * E i * P) = P := by
      have hterm : ∀ i : ι, P * (E i)ᴴ * E i * P = P * ((E i)ᴴ * E i) * P := by
        intro i; rw [Matrix.mul_assoc P]
      simp only [hterm]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE, Matrix.mul_one, hPi]
    exact smul_proj_inj hP0 (by rw [← e1, e2, one_smul])
  have hddsum : ∑ k, (dd k : ℂ) = 1 := by
    rw [← htr, Matrix.trace]
    simpa [Matrix.diag] using hcsum
  obtain ⟨S, hS⟩ : ∃ S : ι → Matrix d d ℂ,
      S = fun k => ((Real.sqrt (dd k) : ℂ))⁻¹ • (P * (F k)ᴴ) := ⟨_, rfl⟩
  have hSadj : ∀ k, (S k)ᴴ = ((Real.sqrt (dd k) : ℂ))⁻¹ • (F k * P) := by
    intro k
    rw [hS]
    simp [conjTranspose_mul, hPh, Complex.conj_ofReal]
  have hF0 : ∀ l, dd l = 0 → F l * P = 0 := by
    intro l hl
    have h1 : (F l * P)ᴴ * (F l * P) = 0 := by
      rw [conjTranspose_mul, hPh, ← Matrix.mul_assoc, hFKL l l, if_pos rfl, hl]
      simp
    exact conjTranspose_mul_self_eq_zero.mp h1
  have hsqrt_mul : ∀ k, ((Real.sqrt (dd k) : ℂ)) * ((Real.sqrt (dd k) : ℂ)) = (dd k : ℂ) := by
    intro k; norm_cast; rw [Real.mul_self_sqrt (hnn k)]
  have hSF : ∀ k l, S k * F l * P = if k = l then ((Real.sqrt (dd k) : ℂ)) • P else 0 := by
    intro k l
    have hrw : S k * F l * P = ((Real.sqrt (dd k) : ℂ))⁻¹ • (P * (F k)ᴴ * F l * P) := by
      rw [hS]; simp
    rw [hrw, hFKL k l]
    by_cases hkl : k = l
    · rw [if_pos hkl, if_pos hkl, smul_smul]
      congr 1
      have := real_inv_sqrt_mul_self (hnn k)
      exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) this
    · rw [if_neg hkl, if_neg hkl]; simp
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix d d ℂ, Q = ∑ k, (S k)ᴴ * S k := ⟨_, rfl⟩
  have hQF : ∀ l, Q * (F l * P) = F l * P := by
    intro l
    rw [hQdef, Finset.sum_mul]
    have hterm : ∀ k : ι, (S k)ᴴ * S k * (F l * P) = if k = l then F l * P else 0 := by
      intro k
      have h1 : (S k)ᴴ * S k * (F l * P) = (S k)ᴴ * (S k * F l * P) := by
        simp [Matrix.mul_assoc]
      rw [h1, hSF k l]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl, hSadj k, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          Matrix.mul_assoc, hPi]
        rcases eq_or_lt_of_le (hnn k) with h0 | h0
        · rw [hF0 k h0.symm]; simp
        · have hs : (Real.sqrt (dd k) : ℂ) ≠ 0 := by
            simpa using Real.sqrt_ne_zero'.mpr h0
          rw [inv_mul_cancel₀ hs, one_smul]
      · rw [if_neg hkl, if_neg hkl, Matrix.mul_zero]
    simp only [hterm]
    simp
  have hQh : Qᴴ = Q := by
    rw [hQdef, conjTranspose_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hQS : ∀ l, Q * (S l)ᴴ = (S l)ᴴ := by
    intro l; rw [hSadj l, Matrix.mul_smul, hQF l]
  have hQQ : Q * Q = Q := by
    nth_rewrite 2 [hQdef]
    rw [Finset.mul_sum]
    have hterm : ∀ l : ι, Q * ((S l)ᴴ * S l) = (S l)ᴴ * S l := fun l => by
      rw [← Matrix.mul_assoc, hQS l]
    simp only [hterm]
    exact hQdef.symm
  obtain ⟨Rops, hRops⟩ : ∃ Rops : Option ι → Matrix d d ℂ,
      Rops = fun x => x.elim (1 - Q) S := ⟨_, rfl⟩
  have hRnone : Rops none = 1 - Q := by simp [hRops]
  have hRsome : ∀ j, Rops (some j) = S j := by intro j; simp [hRops]
  have hcard : Fintype.card (Option ι) = Fintype.card ι + 1 := by simp
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card ι + 1) ≃ Option ι) :=
    ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  refine ⟨Fintype.card ι + 1, fun n => Rops (e n), ?_, ?_⟩
  · rw [Equiv.sum_comp e (fun x => (Rops x)ᴴ * Rops x), Fintype.sum_option, hRnone,
      conjTranspose_sub, conjTranspose_one, hQh]
    have hsq : (1 - Q) * (1 - Q) = 1 - Q := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQQ]
      simp
    rw [hsq]
    have : ∑ j, (Rops (some j))ᴴ * Rops (some j) = Q := by
      rw [hQdef]
      exact Finset.sum_congr rfl fun j _ => by rw [hRsome j]
    rw [this]
    abel
  · intro ρ hρ
    rw [Equiv.sum_comp e (fun x => ∑ i, (Rops x * E i) * ρ * (Rops x * E i)ᴴ)]
    have step1 : ∀ x : Option ι, ∑ i, (Rops x * E i) * ρ * (Rops x * E i)ᴴ
        = ∑ k, (Rops x * F k * P) * ρ * (Rops x * F k * P)ᴴ := by
      intro x
      rw [sum_kraus_conj, ← hFchan ρ, ← sum_kraus_conj]
      exact Finset.sum_congr rfl fun k _ => kraus_restrict hPh (Rops x * F k) hρ
    simp only [step1]
    rw [Fintype.sum_option]
    have hnone : ∑ k, (Rops none * F k * P) * ρ * (Rops none * F k * P)ᴴ = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hz : Rops none * F k * P = 0 := by
        rw [hRnone, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul,
          Matrix.mul_assoc Q (F k) P, hQF k, sub_self]
      rw [hz]; simp
    rw [hnone, zero_add]
    have hsome : ∀ j : ι, ∑ k, (Rops (some j) * F k * P) * ρ * (Rops (some j) * F k * P)ᴴ
        = (dd j : ℂ) • ρ := by
      intro j
      have hterm : ∀ k : ι, (Rops (some j) * F k * P) * ρ * (Rops (some j) * F k * P)ᴴ
          = if j = k then (dd j : ℂ) • ρ else 0 := by
        intro k
        rw [hRsome j, hSF j k]
        by_cases hjk : j = k
        · rw [if_pos hjk, if_pos hjk, smul_real_proj_conj hPh, hρ, Real.mul_self_sqrt (hnn j)]
        · rw [if_neg hjk, if_neg hjk]; simp
      simp only [hterm]
      simp
    simp only [hsome]
    rw [← Finset.sum_smul, hddsum, one_smul]

/-! ## The Knill–Laflamme theorem -/

/-- **Knill–Laflamme theorem**: a code (given by the orthogonal projector `P` onto a nonzero
code subspace) corrects the error set `E` (which forms a quantum channel,
`∑ i, (E i)ᴴ * E i = 1`) if and only if the Knill–Laflamme conditions
`P (E i)ᴴ (E j) P = c i j • P` hold. -/
theorem knill_laflamme {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ}
    (hPh : Pᴴ = P) (hPi : P * P = P) (hP0 : P ≠ 0) (hE : ∑ i, (E i)ᴴ * E i = 1) :
    Correctable P E ↔ KLConditions P E :=
  ⟨correctable_imp_klConditions hPh hPi hP0, klConditions_imp_correctable hPh hPi hP0 hE⟩

/-- Sanity check that the hypotheses of `QI.knill_laflamme` are satisfiable: the noiseless
channel on the whole space is correctable. -/
example : Correctable (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ : Unit => 1) :=
  (knill_laflamme (by simp) (by simp) one_ne_zero (by simp)).mpr ⟨fun _ _ => 1, by simp⟩

end QI

