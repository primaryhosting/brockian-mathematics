/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem corrects_of_diag {P : Matrix n n ℂ} (hP : IsProj P) {F : ι → Matrix n n ℂ}
    {d : ι → ℝ} (hd : ∀ a, 0 ≤ d a)
    (hF : ∀ a b, P * (F a)ᴴ * F b * P = (if a = b then ((d a : ℝ) : ℂ) else 0) • P) :
    Corrects P F := by
  classical
  set Q : ι → Matrix n n ℂ :=
    fun a => ((1 / d a : ℝ) : ℂ) • (F a * P * (F a)ᴴ) with hQdef
  set Rk : ι ⊕ Unit → Matrix n n ℂ :=
    Sum.elim (fun a => ((1 / Real.sqrt (d a) : ℝ) : ℂ) • (P * (F a)ᴴ))
      (fun _ => 1 - ∑ a, Q a) with hRdef
  -- `Q a` is a family of mutually orthogonal projectors
  have hQherm : ∀ a, (Q a)ᴴ = Q a := by
    intro a
    simp only [hQdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP.herm, RCLike.star_def, Complex.conj_ofReal,
      mul_assoc]
  have hQmul : ∀ a b, Q a * Q b = if a = b then Q a else 0 := by
    intro a b
    have hmid : F a * P * (F a)ᴴ * (F b * P * (F b)ᴴ)
        = F a * (P * (F a)ᴴ * F b * P) * (F b)ᴴ := by simp only [mul_assoc]
    have expand : Q a * Q b
        = (((1 / d a : ℝ) : ℂ) * ((1 / d b : ℝ) : ℂ) *
            (if a = b then ((d a : ℝ) : ℂ) else 0)) • (F a * P * (F b)ᴴ) := by
      simp only [hQdef]
      rw [smul_mul, Matrix.mul_smul, smul_smul, hmid, hF a b, Matrix.mul_smul, smul_mul,
        smul_smul]
    rw [expand]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
      simp only [hQdef]
      congr 1
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      norm_cast
      rcases eq_or_ne (d a) 0 with h0 | h0
      · simp [h0]
      · field_simp
    · rw [if_neg hab, if_neg hab]
      simp
  have hQsq : (∑ a, Q a) * (∑ a, Q a) = ∑ a, Q a := by
    calc (∑ a, Q a) * (∑ b, Q b) = ∑ a, ∑ b, Q a * Q b := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
      _ = ∑ a, Q a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_congr rfl fun b _ => hQmul a b]
          simp
  have hQsumherm : (∑ a, Q a)ᴴ = ∑ a, Q a := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun a _ => hQherm a
  -- the recovery operators form a channel
  have hsum : ∑ k, (Rk k)ᴴ * Rk k = 1 := by
    have h1 : ∀ a, (Rk (Sum.inl a))ᴴ * Rk (Sum.inl a) = Q a := by
      intro a
      have hpp : (F a * P) * (P * (F a)ᴴ) = F a * P * (F a)ᴴ := by
        rw [← mul_assoc, mul_assoc (F a) P P, hP.idem]
      simp only [hRdef, Sum.elim_inl, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hP.herm, RCLike.star_def, Complex.conj_ofReal,
        smul_mul, Matrix.mul_smul, smul_smul, hpp, hQdef]
      congr 1
      rw [← Complex.ofReal_mul]
      norm_cast
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (hd a)]
    have h2 : (Rk (Sum.inr ()))ᴴ * Rk (Sum.inr ()) = 1 - ∑ a, Q a := by
      have hexp : ((1 : Matrix n n ℂ) - ∑ a, Q a) * (1 - ∑ a, Q a)
          = 1 - (∑ a, Q a) - (∑ a, Q a) + (∑ a, Q a) * (∑ a, Q a) := by
        noncomm_ring
      simp only [hRdef, Sum.elim_inr, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        hQsumherm]
      rw [hexp, hQsq]
      abel
    rw [Fintype.sum_sum_type, Finset.sum_congr rfl fun a _ => h1 a]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [h2]
    abel
  refine corrects_of Rk hsum ?_
  intro v hv hn
  have hipd : ∀ b, ip (F b *ᵥ v) (F b *ᵥ v) = ((d b : ℝ) : ℂ) := by
    intro b
    conv_lhs => rw [← hv]
    rw [← ip_sandwich hP, hF b b, if_pos rfl, smul_mulVec, hv, ip_smul_right, hn, mul_one]
  -- action of `P * (F a)ᴴ` on the errored code states
  have hact : ∀ a b : ι, (P * (F a)ᴴ) *ᵥ (F b *ᵥ v)
      = (if a = b then ((d a : ℝ) : ℂ) else 0) • v := by
    intro a b
    have hstep : (P * (F a)ᴴ) *ᵥ (F b *ᵥ v) = (P * (F a)ᴴ * F b * P) *ᵥ v := by
      conv_lhs => rw [← hv]
      rw [mulVec_mulVec, mulVec_mulVec]
    rw [hstep, hF a b, smul_mulVec, hv]
  have hFv0 : ∀ b, d b = 0 → F b *ᵥ v = 0 := fun b hb =>
    ip_self_eq_zero (by rw [hipd b, hb]; simp)
  have hRinl : ∀ a b : ι, (Rk (Sum.inl a) * F b) *ᵥ v
      = (if a = b then ((Real.sqrt (d a) : ℝ) : ℂ) else 0) • v := by
    intro a b
    rw [← mulVec_mulVec]
    simp only [hRdef, Sum.elim_inl, smul_mulVec, hact a b, smul_smul]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
      congr 1
      rw [← Complex.ofReal_mul]
      norm_cast
      rcases eq_or_lt_of_le (hd a) with h0 | h0
      · simp [← h0]
      · field_simp
        rw [Real.sq_sqrt (hd a)]
    · rw [if_neg hab, if_neg hab]
      simp
  have hQsumact : ∀ b : ι, (∑ a, Q a) *ᵥ (F b *ᵥ v) = F b *ᵥ v := by
    intro b
    rw [Matrix.sum_mulVec]
    have hterm : ∀ a, Q a *ᵥ (F b *ᵥ v) = if a = b then F b *ᵥ v else 0 := by
      intro a
      have hexp : Q a *ᵥ (F b *ᵥ v)
          = (((1 / d a : ℝ) : ℂ) * (if a = b then ((d a : ℝ) : ℂ) else 0)) • (F a *ᵥ v) := by
        simp only [hQdef, smul_mulVec, mul_assoc]
        rw [← mulVec_mulVec, hact a b, mulVec_smul, smul_smul]
      rw [hexp]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_pos rfl]
        rcases eq_or_ne (d a) 0 with h0 | h0
        · rw [h0]
          simp [hFv0 a h0]
        · rw [← Complex.ofReal_mul, show (1 / d a) * d a = 1 from by field_simp]
          simp
      · rw [if_neg hab, if_neg hab]
        simp
    rw [Finset.sum_congr rfl fun a _ => hterm a]
    simp
  have hRinr : ∀ b : ι, (Rk (Sum.inr ()) * F b) *ᵥ v = 0 := by
    intro b
    rw [← mulVec_mulVec]
    simp only [hRdef, Sum.elim_inr, Matrix.sub_mulVec, Matrix.one_mulVec, hQsumact b]
    simp
  -- assemble
  rw [Fintype.sum_sum_type]
  have hleft : ∀ a : ι, ∑ b, outer ((Rk (Sum.inl a) * F b) *ᵥ v)
      = ((d a : ℝ) : ℂ) • outer v := by
    intro a
    rw [Finset.sum_congr rfl fun b _ => congrArg outer (hRinl a b),
      Finset.sum_eq_single a]
    · rw [if_pos rfl, outer_smul]
      congr 1
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hd a)]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), zero_smul, outer_zero]
    · intro hcon
      exact absurd (Finset.mem_univ a) hcon
  rw [Finset.sum_congr rfl fun a _ => hleft a]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.sum_congr rfl fun b _ => congrArg outer (hRinr b)]
  simp only [outer_zero, Finset.sum_const, smul_zero, add_zero]
  rw [Finset.sum_congr rfl fun b _ => hipd b, ← Finset.sum_smul]

omit [DecidableEq n] [DecidableEq ι] in
