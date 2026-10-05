/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Basic notions -/

/-- The real part of the trace of a matrix. -/
noncomputable def rtr (M : Matrix n n 𝕜) : ℝ := RCLike.re M.trace

/-- The squared Frobenius norm `‖M‖_F² = Re tr (Mᴴ M)`. -/
noncomputable def froSq (M : Matrix n n 𝕜) : ℝ := rtr (Mᴴ * M)

/-- The positive index of inertia of a Hermitian matrix: the number of its positive
eigenvalues (counted with multiplicity). -/
noncomputable def posIndex {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : ℕ :=
  Nat.card {i // 0 < hQ.eigenvalues i}

/-! ### Elementary trace facts -/

omit [DecidableEq n] in
lemma rtr_nonneg {A : Matrix n n 𝕜} (h : A.PosSemidef) : 0 ≤ rtr A :=
  (RCLike.nonneg_iff.mp h.trace_nonneg).1

omit [DecidableEq n] in
lemma rtr_add (A B : Matrix n n 𝕜) : rtr (A + B) = rtr A + rtr B := by
  simp [rtr, Matrix.trace_add]

omit [DecidableEq n] in
lemma rtr_sub (A B : Matrix n n 𝕜) : rtr (A - B) = rtr A - rtr B := by
  simp [rtr, Matrix.trace_sub]

omit [DecidableEq n] in
lemma rtr_smul (t : ℝ) (A : Matrix n n 𝕜) : rtr ((t : 𝕜) • A) = t * rtr A := by
  simp [rtr, Matrix.trace_smul, RCLike.smul_re]

omit [DecidableEq n] in
lemma rtr_mul_comm (A B : Matrix n n 𝕜) : rtr (A * B) = rtr (B * A) := by
  simp [rtr, Matrix.trace_mul_comm A B]

omit [DecidableEq n] in
lemma rtr_nonpos_of_neg_posSemidef {A : Matrix n n 𝕜} (h : (-A).PosSemidef) : rtr A ≤ 0 := by
  have h' := rtr_nonneg h
  simp only [rtr, Matrix.trace_neg, map_neg, neg_nonneg] at h'
  simpa [rtr] using h'

omit [DecidableEq n] in
lemma froSq_nonneg (M : Matrix n n 𝕜) : 0 ≤ froSq M :=
  rtr_nonneg (Matrix.posSemidef_conjTranspose_mul_self M)

omit [DecidableEq n] in
/-- `2 Re tr (M X) ≤ ‖M‖_F² + ‖X‖_F²` for Hermitian `M` and `X`. -/
lemma two_mul_rtr_mul_le {M X : Matrix n n 𝕜} (hM : M.IsHermitian) (hX : X.IsHermitian) :
    2 * rtr (M * X) ≤ froSq M + froSq X := by
  have h0 : 0 ≤ froSq (M - X) := froSq_nonneg _
  have hMX : (M - X)ᴴ = M - X := by rw [Matrix.conjTranspose_sub, hM.eq, hX.eq]
  have hexp : froSq (M - X) = froSq M - 2 * rtr (M * X) + froSq X := by
    rw [froSq, hMX, froSq, froSq, hM.eq, hX.eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      rtr_sub, rtr_sub, rtr_sub, rtr_mul_comm X M]
    ring
  linarith

/-! ### Hermitian projections -/

variable {E : Matrix n n 𝕜}

omit [Fintype n] in
lemma proj_compl_herm (hE : E.IsHermitian) : (1 - E : Matrix n n 𝕜).IsHermitian := by
  show (1 - E : Matrix n n 𝕜)ᴴ = 1 - E
  rw [Matrix.conjTranspose_sub, hE.eq, Matrix.conjTranspose_one]

lemma proj_compl_sq (hE2 : E * E = E) : (1 - E) * (1 - E) = (1 : Matrix n n 𝕜) - E := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hE2]; simp

omit [DecidableEq n] in
lemma conj_herm {S : Matrix n n 𝕜} (hE : E.IsHermitian) (hS : S.IsHermitian) :
    (E * S * E).IsHermitian := by
  show (E * S * E)ᴴ = E * S * E
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hE.eq, hS.eq, Matrix.mul_assoc]

omit [DecidableEq n] in
lemma rtr_conj_proj (hE2 : E * E = E) (M : Matrix n n 𝕜) : rtr (E * M * E) = rtr (M * E) := by
  rw [rtr_mul_comm (E * M) E, ← Matrix.mul_assoc, hE2, rtr_mul_comm]

/-- Splitting the trace along a Hermitian projection and its complement. -/
lemma rtr_proj_split (hE2 : E * E = E) (M : Matrix n n 𝕜) :
    rtr (E * M * E) + rtr ((1 - E) * M * (1 - E)) = rtr M := by
  rw [rtr_conj_proj hE2, rtr_conj_proj (proj_compl_sq hE2), ← rtr_add, ← Matrix.mul_add]
  simp

omit [DecidableEq n] in
lemma froSq_mul_proj_right {F : Matrix n n 𝕜} (hF : F.IsHermitian) (hF2 : F * F = F)
    (M : Matrix n n 𝕜) : froSq (M * F) = rtr (Mᴴ * M * F) := by
  have e1 : (M * F)ᴴ * (M * F) = F * (Mᴴ * M * F) := by
    rw [Matrix.conjTranspose_mul, hF.eq]; simp [Matrix.mul_assoc]
  rw [froSq, e1, rtr_mul_comm, Matrix.mul_assoc (Mᴴ * M) F F, hF2]

lemma froSq_split_left (hE : E.IsHermitian) (hE2 : E * E = E) (M : Matrix n n 𝕜) :
    froSq M = froSq (E * M) + froSq ((1 - E) * M) := by
  have hc := proj_compl_herm hE
  have h1 : froSq (E * M) = rtr (Mᴴ * E * M) := by
    rw [froSq, Matrix.conjTranspose_mul, hE.eq, ← Matrix.mul_assoc, Matrix.mul_assoc Mᴴ E E, hE2]
  have h2 : froSq ((1 - E) * M) = rtr (Mᴴ * (1 - E) * M) := by
    rw [froSq, Matrix.conjTranspose_mul, hc.eq, ← Matrix.mul_assoc,
      Matrix.mul_assoc Mᴴ (1 - E) (1 - E), proj_compl_sq hE2]
  rw [h1, h2, froSq, ← rtr_add, ← Matrix.add_mul, ← Matrix.mul_add]
  simp

lemma froSq_split_right (hE : E.IsHermitian) (hE2 : E * E = E) (M : Matrix n n 𝕜) :
    froSq M = froSq (M * E) + froSq (M * (1 - E)) := by
  rw [froSq_mul_proj_right hE hE2, froSq_mul_proj_right (proj_compl_herm hE) (proj_compl_sq hE2),
    froSq, ← rtr_add, ← Matrix.mul_add]
  simp

/-! ### The quadratic bound -/

/-- If `M` is Hermitian and `E` is a Hermitian projection such that the compression of `M` to the
complement of `E` has nonpositive trace, then `2t·tr M - t²·tr E ≤ ‖M‖_F²` for every `t > 0`.
This is the completion of the square `0 ≤ ‖M - tE‖_F²`. -/
lemma quad_bound {M : Matrix n n 𝕜} (hM : M.IsHermitian) (hE : E.IsHermitian) (hE2 : E * E = E)
    {t : ℝ} (ht : 0 < t) (hneg : rtr ((1 - E) * M * (1 - E)) ≤ 0) :
    2 * t * rtr M - t ^ 2 * rtr E ≤ froSq M := by
  have hXh : ((t : 𝕜) • E).IsHermitian := by
    show ((t : 𝕜) • E)ᴴ = (t : 𝕜) • E
    rw [Matrix.conjTranspose_smul, hE.eq]
    simp
  have hfroX : froSq ((t : 𝕜) • E) = t ^ 2 * rtr E := by
    rw [froSq, hXh.eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← RCLike.ofReal_mul,
      rtr_smul, hE2]
    ring
  have hMX : rtr (M * ((t : 𝕜) • E)) = t * rtr (M * E) := by
    rw [Matrix.mul_smul, rtr_smul]
  have hkey : rtr M ≤ rtr (M * E) := by
    have h1 : rtr ((1 - E) * M * (1 - E)) = rtr M - rtr (M * E) := by
      rw [rtr_conj_proj (proj_compl_sq hE2), Matrix.mul_sub, Matrix.mul_one, rtr_sub]
    linarith [hneg, h1.symm.trans_le hneg]
  have hmain := two_mul_rtr_mul_le hM hXh
  rw [hMX, hfroX] at hmain
  have : 2 * t * rtr M ≤ 2 * t * rtr (M * E) := by
    have := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ 2 * t)
    linarith
  linarith

/-! ### Spectral projections -/

lemma conj_diag_mul {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (d e : n → 𝕜) :
    (U * diagonal d * Uᴴ) * (U * diagonal e * Uᴴ) = U * diagonal (d * e) * Uᴴ := by
  rw [show U * diagonal d * Uᴴ * (U * diagonal e * Uᴴ)
      = U * diagonal d * (Uᴴ * U) * diagonal e * Uᴴ by simp [Matrix.mul_assoc], hU]
  simp [Matrix.diagonal_mul_diagonal, Matrix.mul_assoc, Pi.mul_def]

lemma conj_diag_sub {U : Matrix n n 𝕜} (d e : n → 𝕜) :
    (U * diagonal d * Uᴴ) - (U * diagonal e * Uᴴ) = U * diagonal (d - e) * Uᴴ := by
  have hd : (diagonal (d - e) : Matrix n n 𝕜) = diagonal d - diagonal e := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul]

lemma conj_diag_neg {U : Matrix n n 𝕜} (d : n → 𝕜) :
    -(U * diagonal d * Uᴴ) = U * diagonal (-d) * Uᴴ := by
  have h : (diagonal (-d) : Matrix n n 𝕜) = -diagonal d := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [h, Matrix.mul_neg, Matrix.neg_mul]

omit [Fintype n] in
lemma diag_ofReal_herm (d : n → ℝ) :
    (diagonal (RCLike.ofReal ∘ d) : Matrix n n 𝕜)ᴴ = diagonal (RCLike.ofReal ∘ d) := by
  rw [Matrix.diagonal_conjTranspose]; congr 1; ext i; simp

lemma conj_diag_herm {U : Matrix n n 𝕜} (d : n → ℝ) :
    (U * diagonal (RCLike.ofReal ∘ d) * Uᴴ).IsHermitian := by
  show (U * diagonal (RCLike.ofReal ∘ d) * Uᴴ)ᴴ = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    diag_ofReal_herm, Matrix.mul_assoc]

lemma conj_diag_trace {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (d : n → 𝕜) :
    (U * diagonal d * Uᴴ).trace = ∑ i, d i := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one,
    Matrix.trace_diagonal]

/-- Every Hermitian matrix `M` admits a Hermitian projection `E` onto the span of the
eigenvectors with positive eigenvalue: its trace is the positive index of inertia of `M`,
and the compression of `M` to the orthogonal complement is negative semidefinite. -/
lemma exists_spectral_proj {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    ∃ E : Matrix n n 𝕜, E.IsHermitian ∧ E * E = E ∧ rtr E = (posIndex hM : ℝ) ∧
      (-((1 - E) * M * (1 - E))).PosSemidef := by
  classical
  set U : Matrix n n 𝕜 := (hM.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hM.eigenvectorUnitary.2
  have hU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2
  have hspec : M = U * diagonal (RCLike.ofReal ∘ hM.eigenvalues) * Uᴴ := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  set mu : n → ℝ := hM.eigenvalues with hmu
  set g : n → ℝ := fun i => if 0 < mu i then 1 else 0 with hg
  refine ⟨U * diagonal (RCLike.ofReal ∘ g) * Uᴴ, conj_diag_herm g, ?_, ?_, ?_⟩
  · have hff : ((RCLike.ofReal ∘ g) * (RCLike.ofReal ∘ g) : n → 𝕜) = RCLike.ofReal ∘ g := by
      funext i
      by_cases h : 0 < mu i <;> simp [hg, h]
    rw [conj_diag_mul hU, hff]
  · rw [rtr, conj_diag_trace hU,
      show (∑ i, (RCLike.ofReal ∘ g) i : 𝕜) = ((∑ i, g i : ℝ) : 𝕜) by push_cast; rfl,
      RCLike.ofReal_re, hg, posIndex, Finset.sum_boole]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype, hmu]
  · have hone : (1 : Matrix n n 𝕜) = U * diagonal (fun _ => (1 : 𝕜)) * Uᴴ := by
      simp [Matrix.diagonal_one, hU']
    have hsub : ((fun _ => (1 : 𝕜)) - RCLike.ofReal ∘ g : n → 𝕜)
        = RCLike.ofReal ∘ (fun i => 1 - g i) := by
      funext i; simp
    have hcompl : (1 : Matrix n n 𝕜) - U * diagonal (RCLike.ofReal ∘ g) * Uᴴ
        = U * diagonal (RCLike.ofReal ∘ (fun i => 1 - g i)) * Uᴴ := by
      rw [hone, conj_diag_sub, hsub]
    set k : n → ℝ := fun i => (1 - g i) * mu i * (1 - g i) with hk
    have hprod : ((RCLike.ofReal ∘ (fun i => 1 - g i)) * (RCLike.ofReal ∘ mu) *
        (RCLike.ofReal ∘ (fun i => 1 - g i)) : n → 𝕜) = RCLike.ofReal ∘ k := by
      funext i
      simp [hk]
    rw [hcompl, hspec, conj_diag_mul hU, conj_diag_mul hU, hprod, conj_diag_neg]
    have hd : (diagonal (-(RCLike.ofReal ∘ k)) : Matrix n n 𝕜).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      have he : (-(RCLike.ofReal ∘ k) : n → 𝕜) i = ((-(k i) : ℝ) : 𝕜) := by simp
      rw [he]
      refine RCLike.ofReal_nonneg.mpr ?_
      by_cases h : 0 < mu i
      · simp [hk, hg, h]
      · have h' := not_lt.mp h
        simp only [hk, hg, h, if_false, sub_zero, one_mul, mul_one]
        linarith
    exact hd.mul_mul_conjTranspose_same U

/-- For a positive semidefinite matrix, the positive index of inertia is the rank. -/
lemma posIndex_eq_rank {W : Matrix n n 𝕜} (hW : W.PosSemidef) :
    posIndex hW.isHermitian = W.rank := by
  classical
  rw [hW.isHermitian.rank_eq_card_non_zero_eigs, posIndex, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
  have h := hW.eigenvalues_nonneg i
  constructor
  · intro hi; exact ne_of_gt hi
  · intro hi; exact lt_of_le_of_ne h (Ne.symm hi)

/-! ### The rank–trace inequality -/

/-- **Rank–trace inequality** (Lemma 3.2 of the preprint).

Let `P` be positive semidefinite of rank at most `r`, let `Q` be Hermitian with at most `b`
positive eigenvalues, and let `c > 0`. Then
`c·Re tr P - (c²/4)·r + 2c·Re tr Q - c²·b ≤ ‖P + Q‖_F²`,
where `‖M‖_F² = Re tr (Mᴴ M)`. -/
theorem rank_trace_ineq {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtr P - c ^ 2 / 4 * r + 2 * c * rtr Q - c ^ 2 * b ≤ froSq (P + Q) := by
  obtain ⟨E, hE, hE2, hEtr, hEneg⟩ := exists_spectral_proj hQ
  have hF : (1 - E : Matrix n n 𝕜).IsHermitian := proj_compl_herm hE
  have hF2 : (1 - E) * (1 - E) = (1 : Matrix n n 𝕜) - E := proj_compl_sq hE2
  have hS : (P + Q).IsHermitian := hP.isHermitian.add hQ
  -- the compression `R` of `P` to the complement of `E`
  have hRpsd : ((1 - E) * P * (1 - E)).PosSemidef := by
    have h := hP.mul_mul_conjTranspose_same (1 - E)
    rwa [hF.eq] at h
  obtain ⟨G, hG, hG2, hGtr, hGneg⟩ := exists_spectral_proj hRpsd.isHermitian
  -- splitting the Frobenius norm into the four blocks
  have hsplit : froSq (P + Q)
      = (froSq (E * (P + Q) * E) + froSq (E * (P + Q) * (1 - E)))
        + (froSq ((1 - E) * (P + Q) * E) + froSq ((1 - E) * (P + Q) * (1 - E))) := by
    rw [froSq_split_left hE hE2 (P + Q), froSq_split_right hE hE2 (E * (P + Q)),
      froSq_split_right hE hE2 ((1 - E) * (P + Q))]
  have hge : froSq (E * (P + Q) * E) + froSq ((1 - E) * (P + Q) * (1 - E)) ≤ froSq (P + Q) := by
    rw [hsplit]
    have h1 := froSq_nonneg (E * (P + Q) * (1 - E))
    have h2 := froSq_nonneg ((1 - E) * (P + Q) * E)
    linarith
  -- bound on the `E`-block
  have hEcompl : (1 - E) * E = (0 : Matrix n n 𝕜) := by
    rw [Matrix.sub_mul, hE2, Matrix.one_mul, sub_self]
  have hAneg : rtr ((1 - E) * (E * (P + Q) * E) * (1 - E)) ≤ 0 := by
    have hz : (1 - E) * (E * (P + Q) * E) * (1 - E) = 0 := by
      rw [show (1 - E) * (E * (P + Q) * E) = ((1 - E) * E) * ((P + Q) * E) by
        simp [Matrix.mul_assoc], hEcompl]
      simp
    rw [hz]
    simp [rtr]
  have hbA := quad_bound (conj_herm hE hS) hE hE2 hc hAneg
  -- bound on the complementary block
  have hBsplit : (1 - E) * (P + Q) * (1 - E)
      = (1 - E) * P * (1 - E) + (1 - E) * Q * (1 - E) := by
    rw [Matrix.mul_add, Matrix.add_mul]
  have hBneg : rtr ((1 - G) * ((1 - E) * (P + Q) * (1 - E)) * (1 - G)) ≤ 0 := by
    have hexp : (1 - G) * ((1 - E) * (P + Q) * (1 - E)) * (1 - G)
        = (1 - G) * ((1 - E) * P * (1 - E)) * (1 - G)
          + (1 - G) * ((1 - E) * Q * (1 - E)) * (1 - G) := by
      rw [hBsplit, Matrix.mul_add, Matrix.add_mul]
    have t1 : rtr ((1 - G) * ((1 - E) * P * (1 - E)) * (1 - G)) ≤ 0 :=
      rtr_nonpos_of_neg_posSemidef hGneg
    have t2 : rtr ((1 - G) * ((1 - E) * Q * (1 - E)) * (1 - G)) ≤ 0 := by
      refine rtr_nonpos_of_neg_posSemidef ?_
      have hrw : -((1 - G) * ((1 - E) * Q * (1 - E)) * (1 - G))
          = (1 - G) * (-((1 - E) * Q * (1 - E))) * (1 - G)ᴴ := by
        rw [(proj_compl_herm hG).eq]
        simp
      rw [hrw]
      exact hEneg.mul_mul_conjTranspose_same _
    rw [hexp, rtr_add]
    linarith
  have hbB := quad_bound (conj_herm hF hS) hG hG2 (by positivity : (0:ℝ) < c / 2) hBneg
  -- trace bookkeeping
  have hPsplit : rtr (E * P * E) + rtr ((1 - E) * P * (1 - E)) = rtr P := rtr_proj_split hE2 P
  have hQsplit : rtr (E * Q * E) + rtr ((1 - E) * Q * (1 - E)) = rtr Q := rtr_proj_split hE2 Q
  have hAtr : rtr (E * (P + Q) * E) = rtr (E * P * E) + rtr (E * Q * E) := by
    rw [show E * (P + Q) * E = E * P * E + E * Q * E by rw [Matrix.mul_add, Matrix.add_mul],
      rtr_add]
  have hBtr : rtr ((1 - E) * (P + Q) * (1 - E))
      = rtr ((1 - E) * P * (1 - E)) + rtr ((1 - E) * Q * (1 - E)) := by
    rw [hBsplit, rtr_add]
  have ha : 0 ≤ rtr (E * P * E) := by
    refine rtr_nonneg ?_
    have h := hP.mul_mul_conjTranspose_same E
    rwa [hE.eq] at h
  have he : rtr ((1 - E) * Q * (1 - E)) ≤ 0 := rtr_nonpos_of_neg_posSemidef hEneg
  -- rank bounds
  have hEb : rtr E ≤ (b : ℝ) := by
    rw [hEtr]
    exact_mod_cast hb
  have hGr : rtr G ≤ (r : ℝ) := by
    rw [hGtr, posIndex_eq_rank hRpsd]
    have h1 : ((1 - E) * P * (1 - E)).rank ≤ P.rank :=
      le_trans (Matrix.rank_mul_le_left ((1 - E) * P) (1 - E))
        (Matrix.rank_mul_le_right (1 - E) P)
    exact_mod_cast le_trans h1 hr
  -- combine
  have h1 : 0 ≤ c * rtr (E * P * E) := mul_nonneg hc.le ha
  have h2 : 0 ≤ c * (-rtr ((1 - E) * Q * (1 - E))) := mul_nonneg hc.le (by linarith)
  have h3 : 0 ≤ c ^ 2 * ((b : ℝ) - rtr E) := mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ c ^ 2 / 4 * ((r : ℝ) - rtr G) := mul_nonneg (by positivity) (by linarith)
  rw [hAtr] at hbA
  rw [hBtr] at hbB
  nlinarith [hbA, hbB, hge, hPsplit, hQsplit, h1, h2, h3, h4]

end Zeta23Core

