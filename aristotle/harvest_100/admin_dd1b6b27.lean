/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : ℕ}

/-! ## Definitions -/

/-- `P` is (the matrix of) an orthogonal projection onto a nonzero code subspace. -/
structure IsCode (P : Matrix (Fin n) (Fin n) ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for a code with projection `P` and error operators `E`:
there is a matrix of scalars `c` with `P Eₐ† E_b P = c a b • P`. -/
def KnillLaflammeConditions (P : Matrix (Fin n) (Fin n) ℂ)
    (E : Fin m → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : Matrix (Fin m) (Fin m) ℂ, ∀ a b, P * (E a)ᴴ * E b * P = c a b • P

/-- The code with projection `P` corrects the error operators `E` (the Kraus operators of the
error channel): there is a quantum channel, given by Kraus operators `R` with `∑ Rₖ† Rₖ = 1`,
which undoes the error channel on every operator supported on the code. -/
def CorrectsErrors (P : Matrix (Fin n) (Fin n) ℂ)
    (E : Fin m → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (r : ℕ) (R : Fin r → Matrix (Fin n) (Fin n) ℂ),
    (∑ k, (R k)ᴴ * R k = 1) ∧
      ∀ ρ : Matrix (Fin n) (Fin n) ℂ, P * ρ * P = ρ →
        ∑ k, ∑ a, (R k * E a) * ρ * (R k * E a)ᴴ = ρ

/-! ## Elementary vector/matrix lemmas -/

theorem conj_vecMulVec (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    A * vecMulVec x (star x) * Aᴴ = vecMulVec (A *ᵥ x) (star (A *ᵥ x)) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

theorem quad_vecMulVec (w phi : Fin n → ℂ) :
    star phi ⬝ᵥ (vecMulVec w (star w) *ᵥ phi) = (star phi ⬝ᵥ w) * (star w ⬝ᵥ phi) := by
  simp [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

theorem star_dotProduct_comm (x y : Fin n → ℂ) :
    star y ⬝ᵥ x = (starRingEnd ℂ) (star x ⬝ᵥ y) := by
  simp [dotProduct, map_sum, mul_comm]

/-- A vector orthogonal to everything orthogonal to `ψ ≠ 0` is a multiple of `ψ`. -/
theorem scalar_of_orth (v ψ : Fin n → ℂ) (hψ : ψ ≠ 0)
    (key : ∀ phi : Fin n → ℂ, star phi ⬝ᵥ ψ = 0 → star phi ⬝ᵥ v = 0) :
    ∃ t : ℂ, v = t • ψ := by
  set nrm : ℂ := star ψ ⬝ᵥ ψ with hnrm
  have hnrm0 : nrm ≠ 0 := fun h => hψ (dotProduct_star_self_eq_zero.1 h)
  have hnrmconj : (starRingEnd ℂ) nrm = nrm := by rw [hnrm, ← star_dotProduct_comm ψ ψ]
  refine ⟨(star ψ ⬝ᵥ v) / nrm, ?_⟩
  set c : ℂ := (star ψ ⬝ᵥ v) / nrm with hc
  set phi : Fin n → ℂ := v - c • ψ with hphi
  have hcconj : (starRingEnd ℂ) c = (star v ⬝ᵥ ψ) / nrm := by
    rw [hc, map_div₀, hnrmconj, ← star_dotProduct_comm ψ v]
  have hphiψ : star phi ⬝ᵥ ψ = 0 := by
    rw [hphi]
    simp only [star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [RCLike.star_def, hcconj, ← hnrm]
    field_simp
    ring
  have h1 : star phi ⬝ᵥ v = 0 := key phi hphiψ
  have h2 : star phi ⬝ᵥ phi = 0 := by
    rw [hphi, dotProduct_sub, ← hphi, h1, dotProduct_smul, smul_eq_mul, hphiψ]; ring
  have h3 : phi = 0 := dotProduct_star_self_eq_zero.1 h2
  rw [hphi] at h3
  exact sub_eq_zero.1 h3

/-- If a family of Kraus operators maps the rank-one operator `ψψ†` to itself, then each
operator acts on `ψ` as a scalar. -/
theorem kraus_scalar {ι : Type} [Fintype ι] (A : ι → Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ)
    (h : ∑ j, A j * vecMulVec ψ (star ψ) * (A j)ᴴ = vecMulVec ψ (star ψ)) (j : ι) :
    ∃ t : ℂ, A j *ᵥ ψ = t • ψ := by
  rcases eq_or_ne ψ 0 with hψ | hψ
  · exact ⟨0, by simp [hψ]⟩
  refine scalar_of_orth _ ψ hψ ?_
  intro phi hphi
  have h2 := congrArg (fun M => star phi ⬝ᵥ (M *ᵥ phi)) h
  simp only [Matrix.sum_mulVec, dotProduct_sum, conj_vecMulVec, quad_vecMulVec] at h2
  have hz2 : star ψ ⬝ᵥ phi = 0 := by
    rw [star_dotProduct_comm phi ψ, hphi]; simp
  rw [hphi, hz2] at h2
  simp only [mul_zero] at h2
  have h3 : ∀ i : ι, (star phi ⬝ᵥ A i *ᵥ ψ) * (star (A i *ᵥ ψ) ⬝ᵥ phi)
      = ((Complex.normSq (star phi ⬝ᵥ A i *ᵥ ψ) : ℝ) : ℂ) := by
    intro i
    rw [star_dotProduct_comm phi (A i *ᵥ ψ), Complex.mul_conj]
  rw [Finset.sum_congr rfl (fun i _ => h3 i)] at h2
  have h5 : (∑ i, Complex.normSq (star phi ⬝ᵥ A i *ᵥ ψ) : ℝ) = 0 := by
    exact_mod_cast (by push_cast; exact h2 :
      ((∑ i, Complex.normSq (star phi ⬝ᵥ A i *ᵥ ψ) : ℝ) : ℂ) = 0)
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1 h5 j
    (Finset.mem_univ j)
  simpa using h6

/-- An operator which acts as a scalar on every vector of the range of the projection `P`
acts as a fixed scalar on the whole range. -/
theorem scalar_on_range (P M : Matrix (Fin n) (Fin n) ℂ) (hidem : P * P = P) (hP0 : P ≠ 0)
    (h : ∀ ψ : Fin n → ℂ, P *ᵥ ψ = ψ → ∃ t : ℂ, M *ᵥ ψ = t • ψ) :
    ∃ lam : ℂ, M * P = lam • P := by
  have hex : ∃ v : Fin n → ℂ, P *ᵥ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hP0 ?_
    ext i j
    have := congrFun (hc (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  obtain ⟨v₀, hv₀⟩ := hex
  have hrange : ∀ w : Fin n → ℂ, P *ᵥ (P *ᵥ w) = P *ᵥ w := by
    intro w; rw [Matrix.mulVec_mulVec, hidem]
  obtain ⟨ψ₀, hψ₀r, hψ₀0⟩ : ∃ ψ₀ : Fin n → ℂ, P *ᵥ ψ₀ = ψ₀ ∧ ψ₀ ≠ 0 :=
    ⟨P *ᵥ v₀, hrange v₀, hv₀⟩
  obtain ⟨t₀, ht₀⟩ := h ψ₀ hψ₀r
  refine ⟨t₀, Matrix.ext_iff_mulVec.mpr ?_⟩
  intro w
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  obtain ⟨ψ, hψr, hψe⟩ : ∃ ψ : Fin n → ℂ, P *ᵥ ψ = ψ ∧ ψ = P *ᵥ w := ⟨P *ᵥ w, hrange w, rfl⟩
  rw [← hψe]
  rcases eq_or_ne ψ 0 with hz | hz
  · simp [hz]
  obtain ⟨t, ht⟩ := h ψ hψr
  obtain ⟨t', ht'⟩ := h (ψ + ψ₀) (by rw [Matrix.mulVec_add, hψr, hψ₀r])
  rw [Matrix.mulVec_add, ht, ht₀, smul_add] at ht'
  have key : (t' - t) • ψ = (t₀ - t') • ψ₀ := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, ← ht']
    abel
  have keyM : (t' - t) • (M *ᵥ ψ) = (t₀ - t') • (M *ᵥ ψ₀) := by
    have := congrArg (fun v : Fin n → ℂ => M *ᵥ v) key
    simpa only [Matrix.mulVec_smul] using this
  rw [ht, ht₀, smul_smul, smul_smul] at keyM
  have keyM2 : ((t' - t) * (t - t₀)) • ψ = 0 := by
    have e1 : ((t' - t) * (t - t₀)) • ψ = ((t' - t) * t) • ψ - (t₀ * (t' - t)) • ψ := by
      rw [← sub_smul]; ring_nf
    have e2 : (t₀ * (t' - t)) • ψ = ((t₀ - t') * t₀) • ψ₀ := by
      calc (t₀ * (t' - t)) • ψ = t₀ • ((t' - t) • ψ) := by rw [smul_smul]
        _ = t₀ • ((t₀ - t') • ψ₀) := by rw [key]
        _ = ((t₀ - t') * t₀) • ψ₀ := by rw [smul_smul]; ring_nf
    rw [e1, e2, keyM, sub_self]
  have htt : t = t₀ := by
    have h4 := (smul_eq_zero.1 keyM2).resolve_right hz
    rcases mul_eq_zero.1 h4 with h1 | h1
    · have ht'eq : t' = t := by linear_combination h1
      rw [ht'eq, sub_self, zero_smul] at key
      have h5 := (smul_eq_zero.1 key.symm).resolve_right hψ₀0
      linear_combination -h5
    · linear_combination h1
  rw [ht, htt]

/-! ## Correctability implies the Knill–Laflamme conditions -/

theorem knill_laflamme_of_corrects (P : Matrix (Fin n) (Fin n) ℂ)
    (E : Fin m → Matrix (Fin n) (Fin n) ℂ) (hP : IsCode P) (hcorr : CorrectsErrors P E) :
    KnillLaflammeConditions P E := by
  obtain ⟨r, R, hR1, hrec⟩ := hcorr
  have hlam : ∀ k a, ∃ lam : ℂ, (R k * E a) * P = lam • P := by
    intro k a
    refine scalar_on_range P (R k * E a) hP.idem hP.ne_zero ?_
    intro ψ hψ
    have hρ : P * (vecMulVec ψ (star ψ)) * P = vecMulVec ψ (star ψ) := by
      have h1 := conj_vecMulVec P ψ
      rw [hP.herm] at h1
      rw [h1, hψ]
    have h2 := hrec _ hρ
    have h3 : ∑ j : Fin r × Fin m,
        (R j.1 * E j.2) * vecMulVec ψ (star ψ) * (R j.1 * E j.2)ᴴ = vecMulVec ψ (star ψ) := by
      rw [Fintype.sum_prod_type]; exact h2
    exact kraus_scalar (fun j : Fin r × Fin m => R j.1 * E j.2) ψ h3 (k, a)
  choose lam hlam using hlam
  refine ⟨Matrix.of fun a b => ∑ k, (starRingEnd ℂ) (lam k a) * lam k b, ?_⟩
  intro a b
  have step : P * (E a)ᴴ * E b * P = ∑ k, ((R k * E a * P)ᴴ * (R k * E b * P)) := by
    have h1 : P * (E a)ᴴ * E b * P = P * (E a)ᴴ * (∑ k, (R k)ᴴ * R k) * (E b * P) := by
      rw [hR1]; simp [Matrix.mul_assoc]
    rw [h1, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_mul, hP.herm]
    simp [Matrix.mul_assoc]
  rw [step]
  simp only [hlam, Matrix.conjTranspose_smul, hP.herm, Matrix.smul_mul, Matrix.mul_smul,
    hP.idem, smul_smul, RCLike.star_def]
  rw [← Finset.sum_smul]
  simp [mul_comm]

/-! ## Auxiliary lemmas for the converse -/

theorem smul_cancel {P : Matrix (Fin n) (Fin n) ℂ} (hP0 : P ≠ 0) {x y : ℂ}
    (h : x • P = y • P) : x = y := by
  have h2 : (x - y) • P = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hP0)

theorem dot_mulVec_adj (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  simp [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Finset.mul_sum,
    mul_comm, mul_assoc, mul_left_comm]
  exact Finset.sum_comm

theorem quad_form (P M : Matrix (Fin n) (Fin n) ℂ) (hherm : Pᴴ = P) (ψ : Fin n → ℂ)
    (hψ : P *ᵥ ψ = ψ) :
    star ψ ⬝ᵥ ((P * Mᴴ * M * P) *ᵥ ψ) = star (M *ᵥ ψ) ⬝ᵥ (M *ᵥ ψ) := by
  have e : (P * Mᴴ * M * P) *ᵥ ψ = P *ᵥ (Mᴴ *ᵥ (M *ᵥ (P *ᵥ ψ))) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hψ, dot_mulVec_adj P ψ, hherm, hψ, dot_mulVec_adj Mᴴ ψ,
    Matrix.conjTranspose_conjTranspose]

theorem dot_star_self_ofReal (x : Fin n → ℂ) :
    star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  simp [dotProduct, Complex.mul_conj, mul_comm]

theorem sum_normSq_pos {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < ∑ i, Complex.normSq (x i) := by
  rcases Function.ne_iff.1 hx with ⟨i, hi⟩
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact Complex.normSq_pos.2 hi

theorem nonneg_of_quad {v ψ : Fin n → ℂ} (hψ : ψ ≠ 0) {t : ℝ}
    (h : star v ⬝ᵥ v = (t : ℂ) * (star ψ ⬝ᵥ ψ)) : 0 ≤ t := by
  rw [dot_star_self_ofReal, dot_star_self_ofReal] at h
  have h2 : (∑ i, Complex.normSq (v i)) = t * ∑ i, Complex.normSq (ψ i) := by exact_mod_cast h
  nlinarith [sum_normSq_pos hψ, Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    Complex.normSq_nonneg (v i))]

/-- A nonzero projection has a nonzero fixed vector. -/
theorem exists_fixed_vector {P : Matrix (Fin n) (Fin n) ℂ} (hidem : P * P = P) (hP0 : P ≠ 0) :
    ∃ ψ : Fin n → ℂ, P *ᵥ ψ = ψ ∧ ψ ≠ 0 := by
  have hex : ∃ v : Fin n → ℂ, P *ᵥ v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hP0 ?_
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  obtain ⟨v, hv⟩ := hex
  exact ⟨P *ᵥ v, by rw [Matrix.mulVec_mulVec, hidem], hv⟩

/-- Conjugating a sum of Kraus terms. -/
theorem conj_kraus_sum {ι : Type} [Fintype ι] (X : Matrix (Fin n) (Fin n) ℂ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, (X * G a) * ρ * (X * G a)ᴴ = X * (∑ a, G a * ρ * (G a)ᴴ) * Xᴴ := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The unitary mixing of Kraus operators leaves the channel unchanged. -/
theorem kraus_unitary_mix (E : Fin m → Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (hU : U * Uᴴ = 1) :
    ∑ k, (∑ a, U a k • E a) * ρ * (∑ a, U a k • E a)ᴴ = ∑ a, E a * ρ * (E a)ᴴ := by
  have step : ∀ k : Fin m, (∑ a, U a k • E a) * ρ * (∑ a, U a k • E a)ᴴ
      = ∑ a, ∑ b, (U a k * (starRingEnd ℂ) (U b k)) • (E a * ρ * (E b)ᴴ) := by
    intro k
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
      Finset.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  simp only [step]
  rw [Finset.sum_comm]
  have key : ∀ a : Fin m, ∑ k, ∑ b, (U a k * (starRingEnd ℂ) (U b k)) • (E a * ρ * (E b)ᴴ)
      = ∑ b, ((U * Uᴴ) a b) • (E a * ρ * (E b)ᴴ) := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [← Finset.sum_smul]; congr 1
  simp only [key, hU, Matrix.one_apply]
  exact Finset.sum_congr rfl fun a _ => by simp

/-- The mixed error operators satisfy diagonal Knill–Laflamme relations. -/
theorem mixed_kl (P : Matrix (Fin n) (Fin n) ℂ) (E : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (c : Matrix (Fin m) (Fin m) ℂ) (hc : ∀ a b, P * (E a)ᴴ * E b * P = c a b • P)
    (U : Matrix (Fin m) (Fin m) ℂ) (k l : Fin m) :
    P * (∑ a, U a k • E a)ᴴ * (∑ b, U b l • E b) * P = ((Uᴴ * c * U) k l) • P := by
  have expand : P * (∑ a, U a k • E a)ᴴ * (∑ b, U b l • E b) * P
      = ∑ a, ∑ b, ((starRingEnd ℂ) (U a k) * U b l) • (P * (E a)ᴴ * E b * P) := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
      Finset.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  rw [expand]
  simp only [hc, smul_smul, ← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-! ## The Knill–Laflamme conditions imply correctability -/

theorem corrects_of_knill_laflamme (P : Matrix (Fin n) (Fin n) ℂ)
    (E : Fin m → Matrix (Fin n) (Fin n) ℂ) (hP : IsCode P)
    (hE : ∑ a, (E a)ᴴ * E a = 1) (hKL : KnillLaflammeConditions P E) :
    CorrectsErrors P E := by
  obtain ⟨c, hc⟩ := hKL
  obtain ⟨ψ₀, hψ₀r, hψ₀0⟩ := exists_fixed_vector hP.idem hP.ne_zero
  -- `c` is Hermitian
  have hcH : c.IsHermitian := by
    ext a b
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => Mᴴ) (hc a b)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP.herm,
      Matrix.conjTranspose_smul, RCLike.star_def] at h1
    have h2 : c b a • P = (starRingEnd ℂ) (c a b) • P := by
      rw [← hc b a, ← h1]; noncomm_ring
    have h3 := smul_cancel hP.ne_zero h2
    simp [Matrix.conjTranspose_apply, h3]
  set U : Matrix (Fin m) (Fin m) ℂ := (hcH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  set d : Fin m → ℝ := hcH.eigenvalues with hd
  have hUadj : Uᴴ * U = 1 := by
    simpa [hU, Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self hcH.eigenvectorUnitary
  have hUadj' : U * Uᴴ = 1 := by
    simpa [hU, Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem hcH.eigenvectorUnitary.2
  have hdiag : Uᴴ * c * U = diagonal (fun k => ((d k : ℝ) : ℂ)) := by
    have h := hcH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hU, hd, Matrix.star_eq_conjTranspose, Function.comp_def, mul_assoc] using h
  set F : Fin m → Matrix (Fin n) (Fin n) ℂ := fun k => ∑ a, U a k • E a with hF
  have hFF : ∀ k l, P * (F k)ᴴ * F l * P = (if k = l then ((d k : ℝ) : ℂ) else 0) • P := by
    intro k l
    rw [hF]
    rw [mixed_kl P E c hc U k l, hdiag]
    by_cases hkl : k = l
    · subst hkl; simp [Matrix.diagonal_apply_eq]
    · simp [hkl]
  have hEF : ∀ ρ : Matrix (Fin n) (Fin n) ℂ, ∑ k, F k * ρ * (F k)ᴴ = ∑ a, E a * ρ * (E a)ᴴ :=
    fun ρ => kraus_unitary_mix E ρ U hUadj'
  -- the eigenvalues are nonnegative
  have hd0 : ∀ k, 0 ≤ d k := by
    intro k
    have hkk := hFF k k
    rw [if_pos rfl] at hkk
    have h1 : star (F k *ᵥ ψ₀) ⬝ᵥ (F k *ᵥ ψ₀) = ((d k : ℝ) : ℂ) * (star ψ₀ ⬝ᵥ ψ₀) := by
      rw [← quad_form P (F k) hP.herm ψ₀ hψ₀r, hkk, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul, hψ₀r]
    exact nonneg_of_quad hψ₀0 h1
  -- the eigenvalues sum to one
  have htr : ∑ k, ((d k : ℝ) : ℂ) = 1 := by
    have h1 : ∑ a, c a a = 1 := by
      have h2 : P = (∑ a, c a a) • P := by
        calc P = P * (∑ a, (E a)ᴴ * E a) * P := by rw [hE]; simp [hP.idem]
          _ = ∑ a, P * (E a)ᴴ * E a * P := by
              simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
          _ = ∑ a, c a a • P := by simp only [hc]
          _ = (∑ a, c a a) • P := by rw [Finset.sum_smul]
      exact (smul_cancel hP.ne_zero (by rw [one_smul]; exact h2)).symm
    have h3 : c.trace = ∑ k, ((d k : ℝ) : ℂ) := hcH.trace_eq_sum_eigenvalues
    have h4 : c.trace = ∑ a, c a a := rfl
    rw [← h3, h4, h1]
  -- square roots
  set s : Fin m → ℂ := fun k => ((Real.sqrt (d k) : ℝ) : ℂ) with hs
  have hs2 : ∀ k, s k * s k = ((d k : ℝ) : ℂ) := by
    intro k
    have h := Real.mul_self_sqrt (hd0 k)
    simp only [hs]
    rw [← Complex.ofReal_mul, h]
  have hsconj : ∀ k, (starRingEnd ℂ) (s k) = s k := by intro k; simp [hs]
  have hFP0 : ∀ k, d k = 0 → F k * P = 0 := by
    intro k hk
    have h1 : (F k * P)ᴴ * (F k * P) = 0 := by
      have : (F k * P)ᴴ * (F k * P) = P * (F k)ᴴ * F k * P := by
        simp [Matrix.conjTranspose_mul, hP.herm, Matrix.mul_assoc]
      rw [this, hFF k k, hk]
      simp
    exact conjTranspose_mul_self_eq_zero.1 h1
  set V : Fin m → Matrix (Fin n) (Fin n) ℂ := fun k => (s k)⁻¹ • (F k * P) with hV
  have hVP : ∀ k, V k * P = V k := by
    intro k; rw [hV]; simp [Matrix.mul_assoc, hP.idem]
  have hVF : ∀ k l, (V k)ᴴ * (F l * P) = if k = l then s k • P else 0 := by
    intro k l
    have h1 : (V k)ᴴ * (F l * P) = ((starRingEnd ℂ) ((s k)⁻¹)) • (P * (F k)ᴴ * F l * P) := by
      rw [hV]
      simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hP.herm, Matrix.mul_assoc,
        RCLike.star_def]
    rw [h1, hFF k l]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, smul_smul, map_inv₀, hsconj]
      rcases eq_or_ne (d k) 0 with hdk | hdk
      · have hz : s k = 0 := by simp only [hs]; simp [hdk]
        rw [hz, hdk]
        simp
      · have hsk : s k ≠ 0 := by
          simp only [hs, ne_eq, Complex.ofReal_eq_zero]
          exact Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (hd0 k) (Ne.symm hdk))
        congr 1
        rw [← hs2 k]
        field_simp
    · rw [if_neg hkl, if_neg hkl]
      simp
  set Q : Matrix (Fin n) (Fin n) ℂ := ∑ k, V k * (V k)ᴴ with hQ
  have hQh : Qᴴ = Q := by
    rw [hQ]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]
  have hQF : ∀ l, Q * (F l * P) = F l * P := by
    intro l
    rw [hQ, Finset.sum_mul]
    have : ∀ k, (V k * (V k)ᴴ) * (F l * P) = if k = l then F l * P else 0 := by
      intro k
      rw [Matrix.mul_assoc, hVF k l]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl]
        rw [Matrix.mul_smul, hVP k, hV]
        rw [smul_smul]
        rcases eq_or_ne (d k) 0 with hdk | hdk
        · rw [hFP0 k hdk]; simp
        · have hsk : s k ≠ 0 := by
            rw [hs]
            simp only [ne_eq, Complex.ofReal_eq_zero]
            exact Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (hd0 k) (Ne.symm hdk))
          rw [mul_inv_cancel₀ hsk, one_smul]
      · simp [if_neg hkl]
    simp only [this]
    simp
  have hQV : ∀ l, Q * V l = V l := by
    intro l
    rw [hV]
    simp only [Matrix.mul_smul]
    rw [hQF l]
  have hQQ : Q * Q = Q := by
    conv_lhs => rw [hQ]
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mul_assoc, hQV k]
  refine ⟨m + 1, Fin.snoc (fun k => (V k)ᴴ) (1 - Q), ?_, ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.conjTranspose_conjTranspose]
    have h1 : (1 - Q)ᴴ * (1 - Q) = 1 - Q := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQh]
      noncomm_ring [hQQ]
    rw [h1, ← hQ]
    abel
  · intro ρ hρ
    have hPρ : P * ρ = ρ := by rw [← hρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.idem, hρ]
    have hρP : ρ * P = ρ := by
      conv_lhs => rw [← hρ]
      rw [Matrix.mul_assoc, hP.idem, hρ]
    have hswap : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        ∑ a, (X * E a) * ρ * (X * E a)ᴴ = ∑ k, (X * F k) * ρ * (X * F k)ᴴ := by
      intro X
      rw [conj_kraus_sum X E ρ, conj_kraus_sum X F ρ, hEF ρ]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    simp only [hswap]
    have hlast : ∑ k, ((1 - Q) * F k) * ρ * ((1 - Q) * F k)ᴴ = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have : (1 - Q) * F k * ρ = 0 := by
        have h1 : F k * ρ = (F k * P) * ρ := by rw [Matrix.mul_assoc, hPρ]
        rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hQF k]
        simp
      rw [this]
      simp
    rw [hlast, add_zero]
    have hmain : ∀ k' : Fin m, ∑ k, ((V k')ᴴ * F k) * ρ * ((V k')ᴴ * F k)ᴴ
        = ((d k' : ℝ) : ℂ) • ρ := by
      intro k'
      have hterm : ∀ k, ((V k')ᴴ * F k) * ρ * ((V k')ᴴ * F k)ᴴ
          = if k' = k then ((d k' : ℝ) : ℂ) • ρ else 0 := by
        intro k
        have hAP : (V k')ᴴ * F k * P = if k' = k then s k' • P else 0 := by
          rw [Matrix.mul_assoc, hVF k' k]
        have hsplit : ∀ A : Matrix (Fin n) (Fin n) ℂ, (A * P) * ρ * (A * P)ᴴ = A * ρ * Aᴴ := by
          intro A
          rw [Matrix.conjTranspose_mul, hP.herm]
          calc A * P * ρ * (P * Aᴴ) = A * (P * ρ) * (P * Aᴴ) := by rw [Matrix.mul_assoc A P ρ]
            _ = A * ρ * (P * Aᴴ) := by rw [hPρ]
            _ = A * (ρ * P) * Aᴴ := by simp only [Matrix.mul_assoc]
            _ = A * ρ * Aᴴ := by rw [hρP]
        rw [← hsplit ((V k')ᴴ * F k), hAP]
        by_cases hkk : k' = k
        · subst hkk
          rw [if_pos rfl, if_pos rfl]
          rw [Matrix.conjTranspose_smul, hP.herm, RCLike.star_def, hsconj]
          rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPρ, hρP, hs2 k']
        · rw [if_neg hkk, if_neg hkk]
          simp
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      simp
    rw [Finset.sum_congr rfl fun k' _ => hmain k']
    rw [← Finset.sum_smul, htr, one_smul]

/-! ## The Knill–Laflamme theorem -/

/-- **Knill–Laflamme theorem.** A code (with projection `P` onto a nonzero code subspace)
corrects the error channel with Kraus operators `E` if and only if the Knill–Laflamme
conditions `P Eₐ† E_b P = c a b • P` hold. -/
theorem knill_laflamme (P : Matrix (Fin n) (Fin n) ℂ) (E : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hP : IsCode P) (hE : ∑ a, (E a)ᴴ * E a = 1) :
    CorrectsErrors P E ↔ KnillLaflammeConditions P E :=
  ⟨knill_laflamme_of_corrects P E hP, corrects_of_knill_laflamme P E hP hE⟩

/-! ## Sanity checks: the hypotheses and both sides are satisfiable, and neither side is
trivially true. -/

/-- The trivial code with the trivial (identity) error channel is correctable. -/
example : CorrectsErrors (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  refine (knill_laflamme (1 : Matrix (Fin 1) (Fin 1) ℂ) _
    ⟨by simp, by simp, one_ne_zero⟩ (by simp)).2 ⟨1, ?_⟩
  intro a b
  fin_cases a
  fin_cases b
  simp

/-- The two diagonal projections, as an error channel on a qubit. -/
noncomputable def dephasingKraus : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun a => diagonal (fun i => if i = a then 1 else 0)

/-- The full two-dimensional space is not a code correcting the dephasing channel:
the Knill–Laflamme conditions fail, hence by `knill_laflamme` so does correctability. -/
example : ¬ CorrectsErrors (1 : Matrix (Fin 2) (Fin 2) ℂ) dephasingKraus := by
  have hE : ∑ a, (dephasingKraus a)ᴴ * dephasingKraus a = 1 := by
    simp [dephasingKraus, Matrix.diagonal_conjTranspose, Fin.sum_univ_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [knill_laflamme (1 : Matrix (Fin 2) (Fin 2) ℂ) _ ⟨by simp, by simp, one_ne_zero⟩ hE]
  rintro ⟨c, hc⟩
  have h := hc 0 0
  have h1 := congrFun (congrFun h 0) 0
  have h2 := congrFun (congrFun h 1) 1
  simp [dephasingKraus, Matrix.diagonal_conjTranspose] at h1 h2
  rw [← h1] at h2
  exact zero_ne_one h2

end QI

