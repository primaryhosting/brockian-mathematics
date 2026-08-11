/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- A quantum code, given by the orthogonal projection `P` onto the code subspace. -/
structure IsCodeProj (P : Matrix n n ℂ) : Prop where
  /-- The projection is self-adjoint. -/
  herm : Pᴴ = P
  /-- The projection is idempotent. -/
  idem : P * P = P

/-- The Knill–Laflamme conditions for the code with projection `P` and the error set `E`:
there is a matrix of scalars `c` with `P * (E a)ᴴ * (E b) * P = c a b • P` for all errors
`E a`, `E b`. -/
def KnillLaflammeCond (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∃ c : Matrix ι ι ℂ, ∀ a b : ι, P * (E a)ᴴ * E b * P = c a b • P

/-- The code with projection `P` corrects the error set `E`: there is a recovery quantum
operation, given by a trace preserving family of Kraus operators `R k`
(`∑ k, (R k)ᴴ * R k = 1`), which restores every state supported on the code after any one of
the errors `E a` acted on it, up to a factor `c` (independent of the state) accounting for the
fact that a single error `E a` need not be trace preserving.  Operators `ρ` with `P * ρ * P = ρ`
are exactly the linear combinations of density matrices supported on the code, so quantifying
over all of them is the linear extension of the condition on code states.  -/
def CorrectsErrorSet (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∃ (m : ℕ) (R : Fin m → Matrix n n ℂ), (∑ k, (R k)ᴴ * R k = 1) ∧
    ∀ a : ι, ∃ c : ℂ, ∀ ρ : Matrix n n ℂ, P * ρ * P = ρ →
      ∑ k, R k * (E a * ρ * (E a)ᴴ) * (R k)ᴴ = c • ρ

/-- The operator form of correctability: there is a trace preserving family of Kraus operators
`R k` such that each `R k ∘ E a` acts on the code as a scalar. -/
def HasScalarRecovery (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∃ (m : ℕ) (R : Fin m → Matrix n n ℂ), (∑ k, (R k)ᴴ * R k = 1) ∧
    ∀ (a : ι) (k : Fin m), ∃ l : ℂ, R k * E a * P = l • P

section Aux

omit [DecidableEq n] in
lemma vecMulVec_mulVec (y w z : n → ℂ) :
    vecMulVec y w *ᵥ z = (w ⬝ᵥ z) • y := by
  ext i
  simp only [vecMulVec, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    of_apply]
  exact Finset.sum_congr rfl fun x _ => by ring

omit [DecidableEq n] in
lemma mul_vecMulVec (A : Matrix n n ℂ) (y w : n → ℂ) :
    A * vecMulVec y w = vecMulVec (A *ᵥ y) w := by
  ext i j
  simp [vecMulVec, mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul, mul_assoc]

omit [DecidableEq n] in
lemma vecMulVec_mul (B : Matrix n n ℂ) (y w : n → ℂ) :
    vecMulVec y w * B = vecMulVec y (w ᵥ* B) := by
  ext i j
  simp [vecMulVec, vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
/-- If `y` is orthogonal to everything orthogonal to `v`, then `y` is a multiple of `v`. -/
lemma exists_smul_of_orthogonal (v y : n → ℂ)
    (h : ∀ z : n → ℂ, star v ⬝ᵥ z = 0 → star y ⬝ᵥ z = 0) :
    ∃ μ : ℂ, y = μ • v := by
  by_cases hv : v = 0
  · subst hv
    refine ⟨0, ?_⟩
    have h0 := h y (by simp)
    simpa using dotProduct_star_self_eq_zero.mp h0
  · have hnv : star v ⬝ᵥ v ≠ 0 := fun hc => hv (dotProduct_star_self_eq_zero.mp hc)
    refine ⟨(star v ⬝ᵥ y) / (star v ⬝ᵥ v), ?_⟩
    have hz : star v ⬝ᵥ (y - ((star v ⬝ᵥ y) / (star v ⬝ᵥ v)) • v) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hnv, sub_self]
    have h1 : star y ⬝ᵥ (y - ((star v ⬝ᵥ y) / (star v ⬝ᵥ v)) • v) = 0 := h _ hz
    have h2 : star (y - ((star v ⬝ᵥ y) / (star v ⬝ᵥ v)) • v)
        ⬝ᵥ (y - ((star v ⬝ᵥ y) / (star v ⬝ᵥ v)) • v) = 0 := by
      rw [star_sub, sub_dotProduct, h1, star_smul, smul_dotProduct, hz]
      simp
    exact sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp h2)

/-- An operator acting as a scalar on every vector of the code acts as a scalar on the code. -/
lemma exists_smul_eq_of_forall_mulVec (P A : Matrix n n ℂ)
    (hA : ∀ v : n → ℂ, ∃ μ : ℂ, A *ᵥ (P *ᵥ v) = μ • (P *ᵥ v)) :
    ∃ l : ℂ, A * P = l • P := by
  by_cases hP0 : P = 0
  · exact ⟨0, by simp [hP0]⟩
  obtain ⟨j, hj⟩ : ∃ j : n, P *ᵥ (Pi.single j (1 : ℂ)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hP0 ?_
    ext i j
    have := congrFun (hc j) i
    simpa [Matrix.mulVec_single_one] using this
  obtain ⟨l, hl⟩ := hA (Pi.single j (1 : ℂ))
  refine ⟨l, ?_⟩
  have key : ∀ w : n → ℂ, A *ᵥ (P *ᵥ w) = l • (P *ᵥ w) := by
    intro w
    obtain ⟨μ, hμ⟩ := hA w
    by_cases hu0 : P *ᵥ w = 0
    · rw [hu0]; simp
    by_cases hdep : ∃ t : ℂ, P *ᵥ w = t • (P *ᵥ Pi.single j (1 : ℂ))
    · obtain ⟨t, ht⟩ := hdep
      rw [ht, Matrix.mulVec_smul, hl, smul_comm]
    · obtain ⟨ν, hν⟩ := hA (w + Pi.single j (1 : ℂ))
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hμ, hl] at hν
      have hcomb : (μ - ν) • (P *ᵥ w) + (l - ν) • (P *ᵥ Pi.single j (1 : ℂ)) = 0 := by
        rw [sub_smul, sub_smul, sub_add_sub_comm, hν, smul_add, sub_self]
      have hμν : μ = ν := by
        by_contra hne
        have hsub : μ - ν ≠ 0 := sub_ne_zero.mpr hne
        refine hdep ⟨(ν - l) / (μ - ν), ?_⟩
        have h3 : (μ - ν) • (P *ᵥ w) = (ν - l) • (P *ᵥ Pi.single j (1 : ℂ)) := by
          have h4 := hcomb
          rw [add_eq_zero_iff_eq_neg, ← neg_smul] at h4
          rw [h4]
          congr 1
          ring
        calc P *ᵥ w = (μ - ν)⁻¹ • ((μ - ν) • (P *ᵥ w)) := by
              rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
          _ = ((ν - l) / (μ - ν)) • (P *ᵥ Pi.single j (1 : ℂ)) := by
              rw [h3, smul_smul, div_eq_inv_mul]
      have hlν : l = ν := by
        have h5 : (l - ν) • (P *ᵥ Pi.single j (1 : ℂ)) = 0 := by
          have h6 := hcomb
          rw [hμν, sub_self, zero_smul, zero_add] at h6
          exact h6
        rcases smul_eq_zero.mp h5 with h' | h'
        · exact sub_eq_zero.mp h'
        · exact absurd h' hj
      rw [hμ, hμν, hlν]
  ext i j'
  have h1 : (A * P) *ᵥ (Pi.single j' (1 : ℂ)) = (l • P) *ᵥ (Pi.single j' (1 : ℂ)) := by
    rw [← Matrix.mulVec_mulVec, key, smul_mulVec]
  have := congrFun h1 i
  simpa [Matrix.mulVec_single_one] using this

end Aux

omit [Fintype ι] [DecidableEq ι] in
/-- If a scalar recovery exists, the recovery channel restores all code states. -/
lemma corrects_of_hasScalarRecovery (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E : ι → Matrix n n ℂ) (h : HasScalarRecovery P E) : CorrectsErrorSet P E := by
  obtain ⟨m, R, hsum, hl⟩ := h
  choose l hl using hl
  refine ⟨m, R, hsum, fun a => ⟨∑ k, l a k * (starRingEnd ℂ) (l a k), fun ρ hρ => ?_⟩⟩
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hstar : P * (E a)ᴴ * (R k)ᴴ = (starRingEnd ℂ) (l a k) • P := by
    have h2 : (R k * E a * P)ᴴ = (l a k • P)ᴴ := by rw [hl a k]
    simpa [conjTranspose_mul, hP.herm, mul_assoc] using h2
  calc R k * (E a * ρ * (E a)ᴴ) * (R k)ᴴ
      = (R k * E a * P) * ρ * (P * (E a)ᴴ * (R k)ᴴ) := by
        conv_lhs => rw [← hρ]
        noncomm_ring
    _ = (l a k • P) * ρ * ((starRingEnd ℂ) (l a k) • P) := by rw [hl a k, hstar]
    _ = (l a k * (starRingEnd ℂ) (l a k)) • ρ := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hρ]
        rw [mul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- Conversely, a recovery channel restoring all code states must act as a scalar on the code. -/
lemma hasScalarRecovery_of_corrects (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E : ι → Matrix n n ℂ) (h : CorrectsErrorSet P E) : HasScalarRecovery P E := by
  obtain ⟨m, R, hsum, hc⟩ := h
  refine ⟨m, R, hsum, fun a k => ?_⟩
  obtain ⟨c, hcc⟩ := hc a
  have hmul : ∀ (A : Matrix n n ℂ) (u : n → ℂ),
      A * vecMulVec u (star u) * Aᴴ = vecMulVec (A *ᵥ u) (star (A *ᵥ u)) := by
    intro A u
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec]
  have key : ∀ v : n → ℂ, ∃ μ : ℂ, (R k * E a) *ᵥ (P *ᵥ v) = μ • (P *ᵥ v) := by
    intro v
    refine exists_smul_of_orthogonal _ _ ?_
    intro z hz
    set u : n → ℂ := P *ᵥ v with hu
    have hPu : P *ᵥ u = u := by rw [hu, Matrix.mulVec_mulVec, hP.idem]
    have hstaru : star u ᵥ* P = star u := by
      have h7 : star (P *ᵥ u) = star u ᵥ* Pᴴ := star_mulVec P u
      rw [hPu, hP.herm] at h7
      exact h7.symm
    have hρ : P * vecMulVec u (star u) * P = vecMulVec u (star u) := by
      rw [mul_vecMulVec, vecMulVec_mul, hPu, hstaru]
    have heq := hcc (vecMulVec u (star u)) hρ
    have hrw : ∀ j : Fin m, R j * (E a * vecMulVec u (star u) * (E a)ᴴ) * (R j)ᴴ
        = vecMulVec ((R j * E a) *ᵥ u) (star ((R j * E a) *ᵥ u)) := by
      intro j
      have h8 : R j * (E a * vecMulVec u (star u) * (E a)ᴴ) * (R j)ᴴ
          = (R j * E a) * vecMulVec u (star u) * (R j * E a)ᴴ := by
        rw [conjTranspose_mul]; noncomm_ring
      rw [h8, hmul]
    rw [Finset.sum_congr rfl fun j _ => hrw j] at heq
    have h2 := congrArg (fun M : Matrix n n ℂ => star z ⬝ᵥ (M *ᵥ z)) heq
    simp only [sum_mulVec, vecMulVec_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, hz, zero_mul, mul_zero] at h2
    have hnorm : ∀ j : Fin m, (star ((R j * E a) *ᵥ u) ⬝ᵥ z) * (star z ⬝ᵥ ((R j * E a) *ᵥ u))
        = ((Complex.normSq (star ((R j * E a) *ᵥ u) ⬝ᵥ z) : ℝ) : ℂ) := by
      intro j
      have h9 : star z ⬝ᵥ ((R j * E a) *ᵥ u)
          = (starRingEnd ℂ) (star ((R j * E a) *ᵥ u) ⬝ᵥ z) := by
        simp [dotProduct, map_sum, mul_comm]
      rw [h9, Complex.mul_conj]
    rw [Finset.sum_congr rfl fun j _ => hnorm j] at h2
    have h3 : ∑ j : Fin m, Complex.normSq (star ((R j * E a) *ᵥ u) ⬝ᵥ z) = 0 := by
      exact_mod_cast h2
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (star ((R j * E a) *ᵥ u) ⬝ᵥ z))).mp h3 k
      (Finset.mem_univ k)
    exact Complex.normSq_eq_zero.mp h4
  have h5 := exists_smul_eq_of_forall_mulVec P (R k * E a) key
  obtain ⟨l, hl⟩ := h5
  exact ⟨l, by rw [← hl]⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A scalar recovery forces the Knill–Laflamme conditions. -/
lemma knillLaflammeCond_of_hasScalarRecovery (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E : ι → Matrix n n ℂ) (h : HasScalarRecovery P E) : KnillLaflammeCond P E := by
  obtain ⟨m, R, hsum, hl⟩ := h
  choose l hl using hl
  refine ⟨Matrix.of fun a b => ∑ k, (starRingEnd ℂ) (l a k) * l b k, fun a b => ?_⟩
  have expand : ∀ k, (R k * E a * P)ᴴ * (R k * E b * P)
      = (P * (E a)ᴴ) * ((R k)ᴴ * R k) * (E b * P) := by
    intro k
    simp only [conjTranspose_mul, hP.herm]
    noncomm_ring
  have h1 : ∑ k, (R k * E a * P)ᴴ * (R k * E b * P) = P * (E a)ᴴ * E b * P := by
    simp only [expand]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one]
    noncomm_ring
  rw [← h1]
  simp only [hl, conjTranspose_smul, hP.herm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hP.idem, Finset.sum_smul, RCLike.star_def, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- Reindexing a finite Kraus family by `Fin (card κ)`. -/
lemma hasScalarRecovery_of_fintype_family {κ : Type*} [Fintype κ] (P : Matrix n n ℂ)
    (E : ι → Matrix n n ℂ) (S : κ → Matrix n n ℂ) (h1 : ∑ o, (S o)ᴴ * S o = 1)
    (h2 : ∀ (a : ι) (o : κ), ∃ l : ℂ, S o * E a * P = l • P) : HasScalarRecovery P E := by
  refine ⟨Fintype.card κ, fun i => S ((Fintype.equivFin κ).symm i), ?_, fun a i => h2 a _⟩
  rw [← h1]
  exact Equiv.sum_comp (Fintype.equivFin κ).symm (fun o => (S o)ᴴ * S o)

/-- The main construction: from a family of errors which is orthogonal on the code (with
"weights" `d k ≥ 0`) and which spans the errors on the code, one builds a recovery. -/
lemma hasScalarRecovery_of_orthogonal_family (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E F : ι → Matrix n n ℂ) (d : ι → ℝ) (hd : ∀ k, 0 ≤ d k)
    (horth : ∀ k l, P * (F k)ᴴ * F l * P = (if k = l then ((d k : ℝ) : ℂ) else 0) • P)
    (hE : ∀ a, ∃ t : ι → ℂ, E a * P = ∑ k, t k • (F k * P)) :
    HasScalarRecovery P E := by
  classical
  set Sk : ι → Matrix n n ℂ :=
    fun k => if 0 < d k then (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ) • (P * (F k)ᴴ) else 0 with hSkdef
  set G : ι → Matrix n n ℂ :=
    fun k => if 0 < d k then (((d k)⁻¹ : ℝ) : ℂ) • (F k * P * (F k)ᴴ) else 0 with hGdef
  have hzero : ∀ k, ¬ (0 < d k) → F k * P = 0 := by
    intro k hk
    have hdk : d k = 0 := le_antisymm (not_lt.mp hk) (hd k)
    refine conjTranspose_mul_self_eq_zero.mp ?_
    have h1 := horth k k
    rw [if_pos rfl, hdk] at h1
    rw [conjTranspose_mul, hP.herm]
    simp only [Complex.ofReal_zero, zero_smul] at h1
    rw [← mul_assoc]
    exact h1
  have hSkG : ∀ k, (Sk k)ᴴ * Sk k = G k := by
    intro k
    by_cases hk : 0 < d k
    · simp only [hSkdef, hGdef, if_pos hk, conjTranspose_smul, conjTranspose_mul, hP.herm,
        conjTranspose_conjTranspose, RCLike.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
      rw [← mul_assoc, mul_assoc (F k) P P, hP.idem]
      congr 1
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (le_of_lt hk)]
    · simp [hSkdef, hGdef, if_neg hk]
  have hGmul : ∀ k l, G k * G l = if k = l then G k else 0 := by
    intro k l
    by_cases hk : 0 < d k
    · by_cases hl : 0 < d l
      · have hkey : F k * P * (F k)ᴴ * (F l * P * (F l)ᴴ)
            = F k * (P * (F k)ᴴ * F l * P) * (F l)ᴴ := by noncomm_ring
        simp only [hGdef, if_pos hk, if_pos hl, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          hkey, horth k l]
        by_cases hkl : k = l
        · subst hkl
          rw [if_pos rfl, if_pos rfl]
          congr 1
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
          congr 1
          field_simp
        · rw [if_neg hkl, if_neg hkl]
          simp
      · simp [hGdef, if_neg hl, if_neg (show ¬ k = l from fun hkl => hl (hkl ▸ hk))]
    · by_cases hkl : k = l
      · subst hkl; simp [hGdef, if_neg hk]
      · simp [hGdef, if_neg hk]
  have hGherm : ∀ k, (G k)ᴴ = G k := by
    intro k
    by_cases hk : 0 < d k
    · simp only [hGdef, if_pos hk, conjTranspose_smul, conjTranspose_mul, hP.herm,
        conjTranspose_conjTranspose, RCLike.star_def, Complex.conj_ofReal]
      rw [← mul_assoc]
    · simp [hGdef, if_neg hk]
  have hSkF : ∀ k l, Sk k * (F l * P)
      = (if k = l then ((Real.sqrt (d k) : ℝ) : ℂ) else 0) • P := by
    intro k l
    by_cases hk : 0 < d k
    · have hkey : P * (F k)ᴴ * (F l * P) = P * (F k)ᴴ * F l * P := by noncomm_ring
      simp only [hSkdef, if_pos hk, Matrix.smul_mul, hkey, horth k l, smul_smul]
      by_cases hkl : k = l
      · rw [if_pos hkl, if_pos hkl]
        congr 1
        rw [← Complex.ofReal_mul]
        congr 1
        rw [inv_mul_eq_div, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hk)),
          Real.mul_self_sqrt (le_of_lt hk)]
      · rw [if_neg hkl, if_neg hkl]
        simp
    · have hdk : d k = 0 := le_antisymm (not_lt.mp hk) (hd k)
      simp [hSkdef, if_neg hk, hdk]
  have hGF : ∀ k l, G k * (F l * P) = if k = l then F l * P else 0 := by
    intro k l
    by_cases hk : 0 < d k
    · have hkey : F k * P * (F k)ᴴ * (F l * P) = F k * (P * (F k)ᴴ * F l * P) := by noncomm_ring
      simp only [hGdef, if_pos hk, Matrix.smul_mul, hkey, horth k l]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl, Matrix.mul_smul, smul_smul]
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hk)]
        simp
      · rw [if_neg hkl, if_neg hkl]
        simp
    · rw [show G k = 0 by simp [hGdef, if_neg hk], zero_mul]
      by_cases hkl : k = l
      · subst hkl; rw [if_pos rfl, hzero k hk]
      · rw [if_neg hkl]
  set Q : Matrix n n ℂ := ∑ k, G k with hQdef
  have hQF : ∀ l, Q * (F l * P) = F l * P := by
    intro l
    rw [hQdef, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun k _ => hGF k l]
    simp
  have hQQ : Q * Q = Q := by
    rw [hQdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_congr rfl fun l _ => hGmul k l]
    simp
  have hQherm : Qᴴ = Q := by
    rw [hQdef, conjTranspose_sum]
    exact Finset.sum_congr rfl fun k _ => hGherm k
  have hQE : ∀ a, Q * (E a * P) = E a * P := by
    intro a
    obtain ⟨t, ht⟩ := hE a
    rw [ht, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_smul, hQF k]
  refine hasScalarRecovery_of_fintype_family (κ := Option ι) P E
    (fun o => o.elim (1 - Q) Sk) ?_ ?_
  · rw [Fintype.sum_option]
    simp only [Option.elim]
    rw [Finset.sum_congr rfl fun k _ => hSkG k, ← hQdef]
    rw [conjTranspose_sub, conjTranspose_one, hQherm]
    noncomm_ring
    rw [hQQ]
    abel
  · rintro a (_ | k)
    · refine ⟨0, ?_⟩
      simp only [Option.elim]
      rw [sub_mul, sub_mul, one_mul, mul_assoc, hQE a]
      simp
    · obtain ⟨t, ht⟩ := hE a
      refine ⟨t k * ((Real.sqrt (d k) : ℝ) : ℂ), ?_⟩
      simp only [Option.elim]
      rw [mul_assoc, ht, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_smul, hSkF k l]]
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl, smul_smul]
      · intro l _ hlk
        rw [if_neg (fun hkl => hlk hkl.symm)]
        simp
      · intro hk
        exact absurd (Finset.mem_univ k) hk

/-- The Knill–Laflamme conditions allow one to build a recovery. -/
lemma hasScalarRecovery_of_knillLaflammeCond (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E : ι → Matrix n n ℂ) (h : KnillLaflammeCond P E) : HasScalarRecovery P E := by
  classical
  obtain ⟨c, hc⟩ := h
  by_cases hP0 : P = 0
  · exact ⟨1, fun _ => 1, by simp, fun a k => ⟨0, by simp [hP0]⟩⟩
  -- a nonzero vector of the code
  obtain ⟨j, hj⟩ : ∃ j : n, P *ᵥ (Pi.single j (1 : ℂ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hP0 ?_
    ext i j
    have := congrFun (hcon j) i
    simpa [Matrix.mulVec_single_one] using this
  set v : n → ℂ := P *ᵥ (Pi.single j (1 : ℂ)) with hvdef
  have hPv : P *ᵥ v = v := by rw [hvdef, Matrix.mulVec_mulVec, hP.idem]
  have hstarv : star v ᵥ* P = star v := by
    have h7 : star (P *ᵥ v) = star v ᵥ* Pᴴ := star_mulVec P v
    rw [hPv, hP.herm] at h7
    exact h7.symm
  have hvv : (0 : ℂ) < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hj
  -- scalars are determined by their action on `P`
  have hscal : ∀ s s' : ℂ, s • P = s' • P → s = s' := by
    intro s s' hss
    have : (s - s') • P = 0 := by rw [sub_smul, hss, sub_self]
    rcases smul_eq_zero.mp this with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hP0
  -- `c` is Hermitian
  have hcH : c.IsHermitian := by
    have hsymm : ∀ a b, (starRingEnd ℂ) (c a b) = c b a := by
      intro a b
      refine hscal _ _ ?_
      have h1 : (P * (E a)ᴴ * E b * P)ᴴ = (c a b • P)ᴴ := by rw [hc a b]
      rw [conjTranspose_smul, hP.herm] at h1
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP.herm, RCLike.star_def] at h1
      rw [← h1, ← hc b a]
      noncomm_ring
    ext a b
    rw [conjTranspose_apply, RCLike.star_def, hsymm b a]
  -- `c` is positive semidefinite
  have hcPSD : c.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hcH fun x => ?_
    set Fx : Matrix n n ℂ := ∑ b, x b • E b with hFx
    have hquad : P * Fxᴴ * Fx * P = (star x ⬝ᵥ (c *ᵥ x)) • P := by
      have expand : P * Fxᴴ * Fx * P
          = ∑ a, ∑ b, ((starRingEnd ℂ) (x a) * x b) • (P * (E a)ᴴ * E b * P) := by
        simp only [hFx, conjTranspose_sum, conjTranspose_smul, RCLike.star_def, Finset.sum_mul,
          Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
      rw [expand]
      have step : ∀ a b, ((starRingEnd ℂ) (x a) * x b) • (P * (E a)ᴴ * E b * P)
          = ((starRingEnd ℂ) (x a) * (c a b * x b)) • P := by
        intro a b
        rw [hc a b, smul_smul]
        ring_nf
      simp only [step, ← Finset.sum_smul]
      congr 1
      simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
    have hLHS : star v ⬝ᵥ ((P * Fxᴴ * Fx * P) *ᵥ v) = star (Fx *ᵥ v) ⬝ᵥ (Fx *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv,
        dotProduct_mulVec, hstarv, dotProduct_mulVec, ← star_mulVec]
    have hRHS : star v ⬝ᵥ (((star x ⬝ᵥ (c *ᵥ x)) • P) *ᵥ v)
        = (star x ⬝ᵥ (c *ᵥ x)) * (star v ⬝ᵥ v) := by
      rw [smul_mulVec, hPv, dotProduct_smul, smul_eq_mul]
    have hkey : (star x ⬝ᵥ (c *ᵥ x)) * (star v ⬝ᵥ v) = star (Fx *ᵥ v) ⬝ᵥ (Fx *ᵥ v) := by
      rw [← hRHS, ← hLHS, hquad]
    have hnn : (0 : ℂ) ≤ (star x ⬝ᵥ (c *ᵥ x)) * (star v ⬝ᵥ v) := by
      rw [hkey]; exact dotProduct_star_self_nonneg _
    rw [Complex.le_def] at hnn ⊢
    rw [Complex.lt_def] at hvv
    simp only [Complex.mul_re, Complex.mul_im, Complex.zero_re, Complex.zero_im] at *
    obtain ⟨h1, h2⟩ := hnn
    obtain ⟨h3, h4⟩ := hvv
    rw [← h4] at h1 h2
    constructor
    · nlinarith
    · nlinarith
  -- diagonalize `c`
  set u : Matrix ι ι ℂ := (hcH.eigenvectorUnitary : Matrix ι ι ℂ) with hudef
  set dd : ι → ℝ := hcH.eigenvalues with hdddef
  have hdnn : ∀ k, 0 ≤ dd k := fun k => hcPSD.eigenvalues_nonneg k
  have hdiag : star u * c * u = diagonal (RCLike.ofReal ∘ dd) := by
    have h8 := hcH.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_star_apply] at h8
  have huu : u * star u = 1 := Matrix.mem_unitaryGroup_iff.mp hcH.eigenvectorUnitary.2
  set F : ι → Matrix n n ℂ := fun k => ∑ a, (u a k) • E a with hFdef
  have horth : ∀ k l, P * (F k)ᴴ * F l * P
      = (if k = l then ((dd k : ℝ) : ℂ) else 0) • P := by
    intro k l
    have expand : P * (F k)ᴴ * F l * P
        = ∑ a, ∑ b, ((starRingEnd ℂ) (u a k) * u b l) • (P * (E a)ᴴ * E b * P) := by
      simp only [hFdef, conjTranspose_sum, conjTranspose_smul, RCLike.star_def, Finset.sum_mul,
        Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
    rw [expand]
    have step : ∀ a b, ((starRingEnd ℂ) (u a k) * u b l) • (P * (E a)ᴴ * E b * P)
        = ((starRingEnd ℂ) (u a k) * (c a b * u b l)) • P := by
      intro a b
      rw [hc a b, smul_smul]
      ring_nf
    simp only [step, ← Finset.sum_smul]
    congr 1
    have hentry : ∑ a, ∑ b, ((starRingEnd ℂ) (u a k) * (c a b * u b l))
        = (star u * c * u) k l := by
      simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
    rw [hentry, hdiag, diagonal_apply]
    by_cases hkl : k = l
    · rw [if_pos hkl, if_pos hkl]; rfl
    · rw [if_neg hkl, if_neg hkl]
  have hE : ∀ a, ∃ t : ι → ℂ, E a * P = ∑ k, t k • (F k * P) := by
    intro a
    refine ⟨fun k => (starRingEnd ℂ) (u a k), ?_⟩
    have hEa : E a = ∑ k, ((starRingEnd ℂ) (u a k)) • F k := by
      simp only [hFdef, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have : ∀ b, ∑ k, ((starRingEnd ℂ) (u a k) * u b k) • E b
          = (if b = a then (1 : ℂ) else 0) • E b := by
        intro b
        rw [← Finset.sum_smul]
        congr 1
        have : ∑ k, (starRingEnd ℂ) (u a k) * u b k = (u * star u) b a := by
          simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [this, huu, Matrix.one_apply]
      rw [Finset.sum_congr rfl fun b _ => this b]
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, one_smul]
      · intro b _ hba
        rw [if_neg hba, zero_smul]
      · intro hcon
        exact absurd (Finset.mem_univ a) hcon
    conv_lhs => rw [hEa]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mul]
  exact hasScalarRecovery_of_orthogonal_family P hP E F dd hdnn horth hE

/-- **Knill–Laflamme theorem**: a code (given by the orthogonal projection `P` onto the code
subspace) corrects the error set `E` if and only if it satisfies the Knill–Laflamme
conditions. -/
theorem knill_laflamme (P : Matrix n n ℂ) (hP : IsCodeProj P) (E : ι → Matrix n n ℂ) :
    CorrectsErrorSet P E ↔ KnillLaflammeCond P E :=
  ⟨fun h => knillLaflammeCond_of_hasScalarRecovery P hP E
      (hasScalarRecovery_of_corrects P hP E h),
   fun h => corrects_of_hasScalarRecovery P hP E (hasScalarRecovery_of_knillLaflammeCond P hP E h)⟩

/-- Sanity check (non-vacuity of `CorrectsErrorSet`): the trivial code consisting of the whole
two-dimensional space does not correct the error set `{1, X}` (`X` the bit flip). -/
theorem not_correctsErrorSet_bitFlip :
    ¬ CorrectsErrorSet (1 : Matrix (Fin 2) (Fin 2) ℂ) ![1, !![0, 1; 1, 0]] := by
  rw [knill_laflamme _ ⟨by simp, by simp⟩]
  rintro ⟨c, hc⟩
  have h01 := hc 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, conjTranspose_one,
    one_mul, mul_one] at h01
  have e01 := congrFun (congrFun h01 0) 1
  simp at e01

end QI

