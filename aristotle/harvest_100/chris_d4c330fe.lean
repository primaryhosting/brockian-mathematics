import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexConjugate
open Matrix

namespace QI

section Frobenius

variable {m n : Type} [Fintype m] [Fintype n]

/-- The squared Frobenius norm of a complex matrix, as a real number. -/
noncomputable def fro (A : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

lemma fro_nonneg (A : Matrix m n ℂ) : 0 ≤ fro A := by
  unfold fro
  positivity

lemma trace_conjTranspose_mul_self (A : Matrix m n ℂ) :
    (Aᴴ * A).trace = (fro A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    fro, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

lemma fro_eq_zero_iff (A : Matrix m n ℂ) : fro A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    unfold fro at h
    have h1 : ∀ i ∈ Finset.univ, (∑ j, ‖A i j‖ ^ 2) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp h
      intro i _
      positivity
    have h2 := h1 i (Finset.mem_univ i)
    have h3 : ∀ j ∈ Finset.univ, ‖A i j‖ ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp h2
      intro j _
      positivity
    have := h3 j (Finset.mem_univ j)
    simpa using this
  · intro h
    subst h
    simp [fro]

end Frobenius



section Defs

variable {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]

/-- `P` is the orthogonal projector onto a (nonzero) code subspace. -/
structure IsCodeProjector (P : Matrix m m ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for the code with projector `P` and the error
operators `E`: `P Eₐ† E_b P = c a b • P` for some matrix of scalars `c`. -/
def KnillLaflammeCondition (P : Matrix m m ℂ) (E : ι → Matrix m m ℂ) : Prop :=
  ∃ c : ι → ι → ℂ, ∀ a b, P * (E a)ᴴ * E b * P = c a b • P

/-- The code with projector `P` corrects the error channel whose Kraus operators are `E`:
there is a quantum channel (given by Kraus operators `R`) which restores every state
supported on the code. -/
def Corrects (P : Matrix m m ℂ) (E : ι → Matrix m m ℂ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (R : κ → Matrix m m ℂ),
    (∑ k, (R k)ᴴ * R k = 1) ∧
      ∀ ρ : Matrix m m ℂ, P * ρ * P = ρ → ∑ k, ∑ a, (R k * E a) * ρ * (R k * E a)ᴴ = ρ

end Defs

section Columns

variable {m : Type} [Fintype m] [DecidableEq m]

/-- Multiplication of a column vector by a `1 × 1` matrix is scalar multiplication. -/
lemma col_mul_one_by_one (v : Matrix m (Fin 1) ℂ) (X : Matrix (Fin 1) (Fin 1) ℂ) :
    v * X = (X 0 0) • v := by
  ext i j
  fin_cases j
  simp [Matrix.mul_apply]
  ring

lemma conjTranspose_mul_self_apply (v : Matrix m (Fin 1) ℂ) :
    (vᴴ * v) 0 0 = (fro v : ℂ) := by
  have h := trace_conjTranspose_mul_self v
  simpa [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_one] using h

lemma trace_mul_conjTranspose_self (v : Matrix m (Fin 1) ℂ) :
    (v * vᴴ).trace = (fro v : ℂ) := by
  rw [Matrix.trace_mul_comm, trace_conjTranspose_mul_self]

/-- If a sum of rank-one positive matrices `u k * (u k)ᴴ` equals the rank-one matrix
`v * vᴴ`, then every `u k` is a scalar multiple of `v`. -/
lemma exists_smul_of_sum_rank_one {κ : Type} [Fintype κ] (v : Matrix m (Fin 1) ℂ) (hv : v ≠ 0)
    (u : κ → Matrix m (Fin 1) ℂ) (h : ∑ k, u k * (u k)ᴴ = v * vᴴ) (k : κ) :
    ∃ l : ℂ, u k = l • v := by
  have hfro : fro v ≠ 0 := fun hc => hv ((fro_eq_zero_iff v).mp hc)
  have hs0 : ((fro v : ℂ)) ≠ 0 := by exact_mod_cast hfro
  set s : ℂ := (fro v : ℂ) with hs
  set N : Matrix m m ℂ := 1 - s⁻¹ • (v * vᴴ) with hN
  have hvvv : v * vᴴ * v = s • v := by
    rw [Matrix.mul_assoc, col_mul_one_by_one, conjTranspose_mul_self_apply]
  have hNv : N * v = 0 := by
    rw [hN, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hvvv, smul_smul,
      inv_mul_cancel₀ hs0, one_smul, sub_self]
  have key : ∑ k, (N * u k) * (N * u k)ᴴ = 0 := by
    have h2 : N * (∑ k, u k * (u k)ᴴ) * Nᴴ = N * (v * vᴴ) * Nᴴ := by rw [h]
    rw [Finset.mul_sum, Finset.sum_mul] at h2
    have h3 : N * (v * vᴴ) * Nᴴ = 0 := by
      rw [← Matrix.mul_assoc, hNv, Matrix.zero_mul, Matrix.zero_mul]
    rw [h3] at h2
    refine h2.symm ▸ ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have keytr : ∑ k : κ, (fro (N * u k) : ℂ) = 0 := by
    have hc := congrArg Matrix.trace key
    rw [Matrix.trace_sum, Matrix.trace_zero] at hc
    rw [← hc]
    exact Finset.sum_congr rfl fun k _ => (trace_mul_conjTranspose_self (N * u k)).symm
  have keyR : ∑ k : κ, fro (N * u k) = 0 := by
    have hcc : ((∑ k : κ, fro (N * u k) : ℝ) : ℂ) = 0 := by push_cast; exact keytr
    exact_mod_cast hcc
  have hzero : fro (N * u k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => fro_nonneg _)).mp keyR k (Finset.mem_univ k)
  have hNu : N * u k = 0 := (fro_eq_zero_iff _).mp hzero
  refine ⟨s⁻¹ * ((vᴴ * u k) 0 0), ?_⟩
  rw [hN, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_eq_zero] at hNu
  calc u k = s⁻¹ • (v * vᴴ * u k) := hNu
    _ = s⁻¹ • (((vᴴ * u k) 0 0) • v) := by rw [Matrix.mul_assoc, col_mul_one_by_one]
    _ = (s⁻¹ * ((vᴴ * u k) 0 0)) • v := by rw [smul_smul]

end Columns

section CodeVectors

variable {m : Type} [Fintype m] [DecidableEq m]

/-- The `j`-th column of a square matrix, viewed as a column vector. -/
def colVec (A : Matrix m m ℂ) (j : m) : Matrix m (Fin 1) ℂ := fun i _ => A i j

lemma mul_colVec (A B : Matrix m m ℂ) (j : m) : A * colVec B j = colVec (A * B) j := by
  ext i x
  simp [colVec, Matrix.mul_apply]

lemma exists_colVec_ne_zero {A : Matrix m m ℂ} (hA : A ≠ 0) : ∃ j, colVec A j ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hA
  ext i j
  have := congrFun (congrFun (hc j) i) 0
  simpa [colVec] using this

/-- If a matrix acts as a scalar on every vector of the code space, it is a scalar multiple
of the code projector on that space. -/
lemma eigen_on_code {P : Matrix m m ℂ} (hP : IsCodeProjector P) (A : Matrix m m ℂ)
    (h : ∀ v : Matrix m (Fin 1) ℂ, P * v = v → ∃ l : ℂ, A * v = l • v) :
    ∃ l : ℂ, A * P = l • P := by
  obtain ⟨j0, hj0⟩ := exists_colVec_ne_zero hP.ne_zero
  set v0 : Matrix m (Fin 1) ℂ := colVec P j0 with hv0def
  have hv0code : P * v0 = v0 := by rw [hv0def, mul_colVec, hP.idem]
  obtain ⟨l, hl⟩ := h v0 hv0code
  refine ⟨l, ?_⟩
  have main : ∀ v : Matrix m (Fin 1) ℂ, P * v = v → A * v = l • v := by
    intro v hv
    obtain ⟨n, hn⟩ := h v hv
    by_cases hcase : ∃ t : ℂ, v = t • v0
    · obtain ⟨t, rfl⟩ := hcase
      rw [Matrix.mul_smul, hl, smul_smul, smul_smul, mul_comm]
    · obtain ⟨n', hn'⟩ := h (v + v0) (by rw [Matrix.mul_add, hv, hv0code])
      have e : n' • v + n' • v0 = n • v + l • v0 := by
        rw [← smul_add, ← hn', Matrix.mul_add, hn, hl]
      have e2 : (n' - n) • v = (l - n') • v0 := by
        rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, e]
        exact add_comm _ _
      have hnn : n' = n := by
        by_contra hc
        apply hcase
        refine ⟨(n' - n)⁻¹ * (l - n'), ?_⟩
        rw [← smul_smul, ← e2, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc), one_smul]
      have hz : (l - n') • v0 = 0 := by rw [← e2, hnn, sub_self, zero_smul]
      have hln : l = n' := by
        rcases smul_eq_zero.mp hz with h1 | h1
        · exact sub_eq_zero.mp h1
        · exact absurd h1 hj0
      rw [hn, hln, hnn]
  ext i j
  have hcol := main (colVec P j) (by rw [mul_colVec, hP.idem])
  rw [mul_colVec] at hcol
  have := congrFun (congrFun hcol i) 0
  simpa [colVec] using this

end CodeVectors

section Forward

variable {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]

/-- A correctable code satisfies the Knill–Laflamme conditions. -/
theorem knillLaflamme_of_corrects {P : Matrix m m ℂ} (hP : IsCodeProjector P)
    {E : ι → Matrix m m ℂ} (h : Corrects P E) : KnillLaflammeCondition P E := by
  obtain ⟨κ, hκ, R, hR1, hcorr⟩ := h
  have hscal : ∀ (k : κ) (a : ι), ∃ l : ℂ, (R k * E a) * P = l • P := by
    intro k a
    refine eigen_on_code hP _ ?_
    intro v hv
    by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0]; simp⟩
    have hvH : vᴴ * P = vᴴ := by
      have h1 : (P * v)ᴴ = vᴴ := by rw [hv]
      rwa [Matrix.conjTranspose_mul, hP.herm] at h1
    have hρ : P * (v * vᴴ) * P = v * vᴴ := by
      simp only [← Matrix.mul_assoc]
      rw [hv, Matrix.mul_assoc, hvH]
    have hsum := hcorr (v * vᴴ) hρ
    have hterm : ∀ (A : Matrix m m ℂ), A * (v * vᴴ) * Aᴴ = (A * v) * (A * v)ᴴ := by
      intro A
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hprod : ∑ p : κ × ι, ((R p.1 * E p.2) * v) * (((R p.1 * E p.2) * v))ᴴ = v * vᴴ := by
      rw [Fintype.sum_prod_type]
      rw [← hsum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => (hterm _).symm
    exact exists_smul_of_sum_rank_one v hv0 _ hprod (k, a)
  choose lam hlam using hscal
  refine ⟨fun a b => ∑ k, star (lam k a) * lam k b, ?_⟩
  intro a b
  have step : ∀ k : κ, (R k * E a * P)ᴴ * (R k * E b * P)
      = (star (lam k a) * lam k b) • P := by
    intro k
    rw [hlam k a, hlam k b, Matrix.conjTranspose_smul, hP.herm, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hP.idem]
  calc P * (E a)ᴴ * E b * P
      = P * (E a)ᴴ * (∑ k, (R k)ᴴ * R k) * E b * P := by rw [hR1, mul_one]
    _ = ∑ k, (P * (E a)ᴴ * ((R k)ᴴ * R k) * E b * P) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ k, ((R k * E a * P)ᴴ * (R k * E b * P)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP.herm]
        noncomm_ring
    _ = ∑ k, (star (lam k a) * lam k b) • P := by
        exact Finset.sum_congr rfl fun k _ => step k
    _ = (∑ k, star (lam k a) * lam k b) • P := by rw [Finset.sum_smul]

end Forward

section Rotation

variable {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]

/-- The error operators rotated by a matrix `U`. -/
noncomputable def rotErr (U : Matrix ι ι ℂ) (E : ι → Matrix m m ℂ) (k : ι) : Matrix m m ℂ := ∑ a, U a k • E a

lemma rotErr_kl {P : Matrix m m ℂ} {E : ι → Matrix m m ℂ} {c : ι → ι → ℂ}
    (hc : ∀ a b, P * (E a)ᴴ * E b * P = c a b • P) (U : Matrix ι ι ℂ) (k l : ι) :
    P * (rotErr U E k)ᴴ * (rotErr U E l) * P
      = ((Uᴴ * (Matrix.of c) * U) k l) • P := by
  have hleft : P * (rotErr U E k)ᴴ = ∑ a, star (U a k) • (P * (E a)ᴴ) := by
    simp only [rotErr, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.mul_sum,
      Matrix.mul_smul]
  have hright : (rotErr U E l) * P = ∑ b, U b l • (E b * P) := by
    simp only [rotErr, Finset.sum_mul, Matrix.smul_mul]
  have hassoc : P * (rotErr U E k)ᴴ * (rotErr U E l) * P
      = (P * (rotErr U E k)ᴴ) * ((rotErr U E l) * P) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, hleft, hright, Finset.sum_mul_sum]
  have hterm : ∀ a b : ι, (star (U a k) • (P * (E a)ᴴ)) * (U b l • (E b * P))
      = (star (U a k) * (c a b * U b l)) • P := by
    intro a b
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hc a b, smul_smul]
    ring_nf
  simp only [hterm, ← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun y _ => (mul_assoc _ _ _).symm

lemma rotErr_channel {E : ι → Matrix m m ℂ} (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1)
    (ρ : Matrix m m ℂ) :
    ∑ k, rotErr U E k * ρ * (rotErr U E k)ᴴ = ∑ a, E a * ρ * (E a)ᴴ := by
  have hexp : ∀ k : ι, rotErr U E k * ρ * (rotErr U E k)ᴴ
      = ∑ a, ∑ b, (U a k * star (U b k)) • (E a * ρ * (E b)ᴴ) := by
    intro k
    simp only [rotErr, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.sum_mul,
      Matrix.smul_mul, Finset.mul_sum, Matrix.mul_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm (star (U b k)) (U a k)]
  simp only [hexp]
  rw [Finset.sum_comm]
  have : ∀ a : ι, ∑ k, ∑ b, (U a k * star (U b k)) • (E a * ρ * (E b)ᴴ)
      = ∑ b, ((U * Uᴴ) a b) • (E a * ρ * (E b)ᴴ) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [this, hU, Matrix.one_apply]

end Rotation

section Aux

variable {m : Type} [Fintype m] [DecidableEq m]

lemma smul_eq_smul_of_ne_zero {P : Matrix m m ℂ} (hP : P ≠ 0) {z w : ℂ}
    (h : z • P = w • P) : z = w := by
  by_contra hne
  apply hP
  have : (z - w) • P = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact h1

lemma fro_pos_of_projector {P : Matrix m m ℂ} (hP : IsCodeProjector P) : 0 < fro P := by
  rcases lt_or_eq_of_le (fro_nonneg P) with h | h
  · exact h
  · exact absurd ((fro_eq_zero_iff P).mp h.symm) hP.ne_zero

lemma trace_projector {P : Matrix m m ℂ} (hP : IsCodeProjector P) :
    P.trace = (fro P : ℂ) := by
  rw [← trace_conjTranspose_mul_self P, hP.herm, hP.idem]

end Aux

end QI

