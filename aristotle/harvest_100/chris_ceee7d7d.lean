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

variable {n A : Type*} [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]

/-- A *code* is given by the orthogonal projection `P` onto the code subspace: `P` is
self-adjoint, idempotent, and nonzero (the code subspace is nontrivial). -/
structure IsCodeProjector (P : Matrix n n ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  nontrivial : P ≠ 0

/-- The error set `E` is the Kraus family of a quantum channel (trace preserving). -/
def IsKrausChannel (E : A → Matrix n n ℂ) : Prop := ∑ a, (E a)ᴴ * E a = 1

/-- The Knill–Laflamme conditions: `P Eₐ† E_b P = c a b • P` for a matrix of scalars `c`. -/
def KnillLaflammeCondition (P : Matrix n n ℂ) (E : A → Matrix n n ℂ) : Prop :=
  ∃ c : A → A → ℂ, ∀ a b, P * (E a)ᴴ * E b * P = c a b • P

/-- `R` is a recovery channel for the code `P` and the error set `E`: it is a channel
(its Kraus operators satisfy `∑ Rₖ† Rₖ = 1`) and the composition of the error channel with
the recovery channel acts as the identity on all states supported on the code. -/
def IsRecovery (P : Matrix n n ℂ) (E : A → Matrix n n ℂ) {K : Type*} [Fintype K]
    (R : K → Matrix n n ℂ) : Prop :=
  (∑ k, (R k)ᴴ * R k = 1) ∧
    ∀ ρ : Matrix n n ℂ, P * ρ * P = ρ → ∑ k, ∑ a, R k * E a * ρ * (E a)ᴴ * (R k)ᴴ = ρ

/-- The code `P` *corrects* the error set `E` if some recovery channel exists. -/
def Corrects (P : Matrix n n ℂ) (E : A → Matrix n n ℂ) : Prop :=
  ∃ (m : ℕ) (R : Fin m → Matrix n n ℂ), IsRecovery P E R

/-! ### Elementary lemmas -/

omit [Fintype n] [DecidableEq n] in
lemma smul_eq_smul_of_ne_zero {P : Matrix n n ℂ} (hP : P ≠ 0) {r s : ℂ}
    (h : r • P = s • P) : r = s := by
  have : (r - s) • P = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 this with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' hP

omit [DecidableEq n] in
lemma conj_mul_vecMulVec (B : Matrix n n ℂ) (x : n → ℂ) :
    B * vecMulVec x (star x) * Bᴴ = vecMulVec (B *ᵥ x) (star (B *ᵥ x)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul', RCLike.star_def,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

omit [DecidableEq n] in
lemma vecMulVec_mulVec (x y v : n → ℂ) :
    (vecMulVec x (star y)) *ᵥ v = (star y ⬝ᵥ v) • x := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

omit [DecidableEq n] in
lemma conj_dotProduct_star (x y : n → ℂ) :
    (starRingEnd ℂ) (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
  simp [dotProduct, map_sum, mul_comm]

omit [DecidableEq n] in
/-- If a sum of rank one positive matrices `|wᵢ⟩⟨wᵢ|` equals `|ψ⟩⟨ψ|` then each `wᵢ` is a
multiple of `ψ`. -/
lemma exists_smul_of_sum_vecMulVec {ι : Type*} [Fintype ι] (w : ι → n → ℂ) (psi : n → ℂ)
    (h : ∑ i, vecMulVec (w i) (star (w i)) = vecMulVec psi (star psi)) (i : ι) :
    ∃ mu : ℂ, w i = mu • psi := by
  have key : ∀ v : n → ℂ, ∑ j, (star (w j) ⬝ᵥ v) * (star v ⬝ᵥ w j)
      = (star psi ⬝ᵥ v) * (star v ⬝ᵥ psi) := by
    intro v
    have := congrArg (fun M : Matrix n n ℂ => star v ⬝ᵥ (M *ᵥ v)) h
    simpa only [Matrix.sum_mulVec, dotProduct_sum, vecMulVec_mulVec, dotProduct_smul,
      smul_eq_mul] using this
  set N : ℂ := star psi ⬝ᵥ psi with hN
  set mu : ℂ := (star psi ⬝ᵥ w i) / N with hmu
  refine ⟨mu, ?_⟩
  set v : n → ℂ := w i - mu • psi with hv
  have hstarv : star v = star (w i) - (starRingEnd ℂ mu) • star psi := by
    simp [hv, star_sub, star_smul]
  have hNconj : (starRingEnd ℂ) N = N := by
    simpa [hN] using conj_dotProduct_star psi psi
  have hvpsi : star v ⬝ᵥ psi = 0 := by
    rw [hstarv, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rcases eq_or_ne psi 0 with hp | hp
    · simp [hp]
    · have hNne : N ≠ 0 := by
        rw [hN]
        exact fun hc => hp (dotProduct_star_self_eq_zero.1 (by simpa using hc))
      have h2 : (starRingEnd ℂ) mu * N = star (w i) ⬝ᵥ psi := by
        rw [hmu, map_div₀, hNconj, conj_dotProduct_star]
        field_simp
      rw [h2, sub_self]
  have hpsiv : star psi ⬝ᵥ v = 0 := by
    have := conj_dotProduct_star v psi
    rw [hvpsi] at this
    simpa using this.symm
  have hsum := key v
  rw [hpsiv, zero_mul] at hsum
  have hzero : ∀ j, star (w j) ⬝ᵥ v = 0 := by
    have hre : ∑ j, ((Complex.normSq (star (w j) ⬝ᵥ v) : ℝ) : ℂ) = 0 := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← conj_dotProduct_star (w j) v, Complex.mul_conj]
    have hre' : ∑ j, Complex.normSq (star (w j) ⬝ᵥ v) = 0 := by exact_mod_cast hre
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hre' j
      (Finset.mem_univ j)
    simpa using Complex.normSq_eq_zero.1 this
  have hvv : star v ⬝ᵥ v = 0 := by
    rw [hstarv, sub_dotProduct, smul_dotProduct, smul_eq_mul, hzero i, hpsiv]
    ring
  have hv0 := dotProduct_star_self_eq_zero.1 hvv
  rw [hv] at hv0
  linear_combination (norm := module) hv0

/-- A projector applied to any vector gives a vector of the code. -/
lemma exists_ne_zero_mem_code {P : Matrix n n ℂ} (hP : IsCodeProjector P) :
    ∃ x : n → ℂ, P *ᵥ x = x ∧ x ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hP.nontrivial (by ext i j; simp [hc i j])
  refine ⟨P *ᵥ (Pi.single j 1), by rw [mulVec_mulVec, hP.idem], ?_⟩
  intro hzero
  exact hij (by simpa [Matrix.mulVec_single_one] using congrFun hzero i)

/-- If every code vector is an eigenvector of `B`, the eigenvalue is constant. -/
lemma exists_const_eigenvalue {P B : Matrix n n ℂ} (hP : IsCodeProjector P)
    (h : ∀ x : n → ℂ, P *ᵥ x = x → ∃ mu : ℂ, B *ᵥ x = mu • x) :
    ∃ lam : ℂ, B * P = lam • P := by
  obtain ⟨p0, hp0, hp0ne⟩ := exists_ne_zero_mem_code hP
  obtain ⟨lam, hlam⟩ := h p0 hp0
  refine ⟨lam, ?_⟩
  have main : ∀ y : n → ℂ, P *ᵥ y = y → B *ᵥ y = lam • y := by
    intro y hy
    obtain ⟨mu, hmu⟩ := h y hy
    obtain ⟨nu, hnu⟩ := h (p0 + y) (by rw [mulVec_add, hp0, hy])
    rw [mulVec_add, hlam, hmu, smul_add] at hnu
    have hkey : (lam - nu) • p0 = (nu - mu) • y := by
      linear_combination (norm := module) hnu
    rcases eq_or_ne lam nu with hln | hln
    · rw [hln, sub_self, zero_smul] at hkey
      rcases smul_eq_zero.1 hkey.symm with h1 | h1
      · rw [hmu, ← sub_eq_zero.1 h1, hln]
      · simp [h1]
    · have hne' : lam - nu ≠ 0 := sub_ne_zero.2 hln
      set t : ℂ := (nu - mu) / (lam - nu) with ht
      have hp0eq : p0 = t • y := by
        have h3 := congrArg (fun z : n → ℂ => (lam - nu)⁻¹ • z) hkey
        simp only [smul_smul, inv_mul_cancel₀ hne', one_smul] at h3
        rw [h3, ht]
        congr 1
        field_simp
      have hy0 : y ≠ 0 := by
        intro hc; rw [hc, smul_zero] at hp0eq; exact hp0ne hp0eq
      have htne : t ≠ 0 := by
        intro hc; rw [hc, zero_smul] at hp0eq; exact hp0ne hp0eq
      have h4 : (t * mu) • y = (lam * t) • y := by
        have h1 : B *ᵥ p0 = (t * mu) • y := by rw [hp0eq, mulVec_smul, hmu, smul_smul]
        have h2 : B *ᵥ p0 = (lam * t) • y := by rw [hlam, hp0eq, smul_smul]
        rw [← h1, h2]
      have h5 : (t * mu - lam * t) • y = 0 := by rw [sub_smul, h4, sub_self]
      rcases smul_eq_zero.1 h5 with h1 | h1
      · have h6 : t * (mu - lam) = 0 := by linear_combination h1
        rcases mul_eq_zero.1 h6 with h2 | h2
        · exact absurd h2 htne
        · rw [hmu, sub_eq_zero.1 h2]
      · exact absurd h1 hy0
  ext i j
  have h7 := main (P *ᵥ Pi.single j 1) (by rw [mulVec_mulVec, hP.idem])
  rw [mulVec_mulVec] at h7
  have hcol := congrFun h7 i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hcol

/-! ### The forward direction: correctability implies the Knill–Laflamme conditions -/

omit [DecidableEq A] in
lemma knill_laflamme_of_corrects (P : Matrix n n ℂ) (E : A → Matrix n n ℂ)
    (hP : IsCodeProjector P) (h : Corrects P E) : KnillLaflammeCondition P E := by
  obtain ⟨m, R, hR1, hR2⟩ := h
  -- each operator `R k * E a` acts on the code as a scalar
  have hEig : ∀ (k : Fin m) (a : A), ∃ lam : ℂ, (R k * E a) * P = lam • P := by
    intro k a
    refine exists_const_eigenvalue hP ?_
    intro x hx
    have hrho : P * (vecMulVec x (star x)) * P = vecMulVec x (star x) := by
      rw [show P * vecMulVec x (star x) * P = P * vecMulVec x (star x) * Pᴴ by rw [hP.herm],
        conj_mul_vecMulVec, hx]
    have hsum := hR2 _ hrho
    have hsum2 : ∑ p : Fin m × A,
        vecMulVec ((R p.1 * E p.2) *ᵥ x) (star ((R p.1 * E p.2) *ᵥ x))
        = vecMulVec x (star x) := by
      rw [Fintype.sum_prod_type, ← hsum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
      rw [show R k * E a * vecMulVec x (star x) * (E a)ᴴ * (R k)ᴴ
          = (R k * E a) * vecMulVec x (star x) * (R k * E a)ᴴ by
        simp [Matrix.conjTranspose_mul, mul_assoc]]
      rw [conj_mul_vecMulVec]
    exact exists_smul_of_sum_vecMulVec _ x hsum2 (k, a)
  choose lam hlam using hEig
  refine ⟨fun a b => ∑ k, star (lam k a) * lam k b, fun a b => ?_⟩
  have step : ∀ k : Fin m, (R k * E a * P)ᴴ * (R k * E b * P)
      = (star (lam k a) * lam k b) • P := by
    intro k
    rw [hlam k a, hlam k b, Matrix.conjTranspose_smul, hP.herm, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hP.idem]
  have expand : ∑ k : Fin m, (R k * E a * P)ᴴ * (R k * E b * P)
      = P * (E a)ᴴ * E b * P := by
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
      show (R k * E a * P)ᴴ * (R k * E b * P)
        = (P * (E a)ᴴ) * ((R k)ᴴ * R k) * (E b * P) by
          simp only [Matrix.conjTranspose_mul, hP.herm]; noncomm_ring]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hR1, Matrix.mul_one]
    noncomm_ring
  rw [← expand, Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => step k, ← Finset.sum_smul]

/-! ### The converse: the Knill–Laflamme conditions imply correctability

The strategy is the standard one: after diagonalizing the matrix `c` of the Knill–Laflamme
conditions one obtains an equivalent Kraus family `F` for the error channel which satisfies
the *diagonal* Knill–Laflamme conditions `P (F x)ᴴ (F y) P = δₓᵧ dₓ P`.  The recovery channel
is then built out of the partial isometries `P (F x)ᴴ / √dₓ`, completed by the projection onto
the orthogonal complement of the (mutually orthogonal) error subspaces. -/

section Diagonal

variable {P : Matrix n n ℂ} {F : A → Matrix n n ℂ} {d : A → ℝ}

/-- The Kraus operators of the recovery channel attached to a diagonal Knill–Laflamme family. -/
noncomputable def recOp (P : Matrix n n ℂ) (F : A → Matrix n n ℂ) (d : A → ℝ) (x : A) :
    Matrix n n ℂ := ((Real.sqrt (d x) : ℂ))⁻¹ • (P * (F x)ᴴ)

/-- The full recovery family: the operators `recOp` together with the complementary projection. -/
noncomputable def recFam (P : Matrix n n ℂ) (F : A → Matrix n n ℂ) (d : A → ℝ) :
    Option A → Matrix n n ℂ
  | none => 1 - ∑ x, (recOp P F d x)ᴴ * recOp P F d x
  | some x => recOp P F d x

lemma sqrt_inv_mul (dx : ℝ) (h : 0 ≤ dx) :
    ((Real.sqrt dx : ℂ))⁻¹ * (dx : ℂ) = (Real.sqrt dx : ℂ) := by
  rcases eq_or_lt_of_le h with h0 | h0
  · simp [← h0]
  · have hs : (Real.sqrt dx : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.2 h0)
    have hsq : (Real.sqrt dx : ℂ) * (Real.sqrt dx : ℂ) = (dx : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]
    field_simp
    rw [pow_two, hsq]

lemma sqrt_inv_sq (dx : ℝ) (h : 0 ≤ dx) :
    ((Real.sqrt dx : ℂ))⁻¹ * ((Real.sqrt dx : ℂ))⁻¹ = ((dx : ℂ))⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]

omit [Fintype A] in
/-- The diagonal Knill–Laflamme coefficients are nonnegative. -/
lemma d_nonneg (hP : IsCodeProjector P)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) (x : A) :
    0 ≤ d x := by
  obtain ⟨psi, hpsi, hpsine⟩ := exists_ne_zero_mem_code hP
  have hps : ((F x * P)ᴴ * (F x * P)).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have heq : (F x * P)ᴴ * (F x * P) = (d x : ℂ) • P := by
    rw [Matrix.conjTranspose_mul, hP.herm,
      ← (by simpa using hFF x x : P * (F x)ᴴ * F x * P = (d x : ℂ) • P)]
    noncomm_ring
  rw [heq] at hps
  have h2 := hps.dotProduct_mulVec_nonneg psi
  rw [Matrix.smul_mulVec, hpsi, dotProduct_smul, smul_eq_mul] at h2
  have hpos : (0 : ℂ) < star psi ⬝ᵥ psi := dotProduct_star_self_pos_iff.2 hpsine
  simp only [Complex.le_def, Complex.lt_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero, add_zero] at h2 hpos
  nlinarith [h2.1, hpos.1]

omit [DecidableEq n] [Fintype A] in
/-- An error with vanishing coefficient annihilates the code. -/
lemma FP_eq_zero (hP : IsCodeProjector P)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) {x : A}
    (hx : d x = 0) : F x * P = 0 := by
  have key : P * (F x)ᴴ * F x * P = 0 := by simpa [hx] using hFF x x
  refine Matrix.conjTranspose_mul_self_eq_zero.1 ?_
  simp only [Matrix.conjTranspose_mul, hP.herm]
  rw [← mul_assoc]
  exact key

/-- The diagonal Knill–Laflamme coefficients sum to one. -/
lemma sum_d_eq_one (hP : IsCodeProjector P)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P)
    (hFsum : ∑ y, (F y)ᴴ * F y = 1) : ∑ y, (d y : ℂ) = 1 := by
  have h1 : ∑ y, P * ((F y)ᴴ * F y) * P = P := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hFsum, Matrix.mul_one, hP.idem]
  have h2 : ∑ y, P * ((F y)ᴴ * F y) * P = (∑ y, (d y : ℂ)) • P := by
    rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) =>
      show P * ((F y)ᴴ * F y) * P = (d y : ℂ) • P by
        rw [← (by simpa using hFF y y : P * (F y)ᴴ * F y * P = (d y : ℂ) • P)]; noncomm_ring,
      ← Finset.sum_smul]
  rw [h2] at h1
  exact smul_eq_smul_of_ne_zero hP.nontrivial (by rw [h1, one_smul])

omit [DecidableEq n] [Fintype A] [DecidableEq A] in
lemma recOp_conj (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x) (x : A) :
    (recOp P F d x)ᴴ * recOp P F d x = ((d x : ℂ))⁻¹ • (F x * P * (F x)ᴴ) := by
  rw [recOp, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hP.herm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show F x * P * (P * (F x)ᴴ) = F x * (P * P) * (F x)ᴴ by noncomm_ring, hP.idem]
  congr 1
  rw [show star ((Real.sqrt (d x) : ℂ))⁻¹ = ((Real.sqrt (d x) : ℂ))⁻¹ by simp]
  exact sqrt_inv_sq _ (hd x)

omit [DecidableEq n] [Fintype A] in
lemma recOp_mul (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) (x y : A) :
    recOp P F d x * F y * P = (if x = y then ((Real.sqrt (d x) : ℝ) : ℂ) else 0) • P := by
  rw [recOp, Matrix.smul_mul, Matrix.smul_mul, show P * (F x)ᴴ * F y * P
    = (if x = y then (d x : ℂ) else 0) • P from hFF x y, smul_smul]
  congr 1
  by_cases h : x = y
  · simp only [if_pos h]
    exact sqrt_inv_mul _ (hd x)
  · simp [h]

omit [DecidableEq n] in
/-- The sum `∑ (recOp x)ᴴ (recOp x)` is an orthogonal projection. -/
lemma pi_idem (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) :
    (∑ x, (recOp P F d x)ᴴ * recOp P F d x) * (∑ x, (recOp P F d x)ᴴ * recOp P F d x)
      = ∑ x, (recOp P F d x)ᴴ * recOp P F d x := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · rw [recOp_conj hP hd, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show F x * P * (F x)ᴴ * (F x * P * (F x)ᴴ) = F x * (P * (F x)ᴴ * F x * P) * (F x)ᴴ by
        noncomm_ring, hFF x x, if_pos rfl, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    rcases eq_or_lt_of_le (hd x) with h0 | h0
    · simp [← h0]
    · have : (d x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
      field_simp
  · intro y _ hy
    rw [recOp_conj hP hd, recOp_conj hP hd, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show F x * P * (F x)ᴴ * (F y * P * (F y)ᴴ) = F x * (P * (F x)ᴴ * F y * P) * (F y)ᴴ by
        noncomm_ring, hFF x y, if_neg hy.symm]
    simp
  · intro h; exact absurd (Finset.mem_univ x) h

omit [DecidableEq n] in
/-- The projection `∑ (recOp x)ᴴ (recOp x)` acts as the identity on all error subspaces. -/
lemma pi_mul (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P)
    (hzero : ∀ x, d x = 0 → F x * P = 0) (y : A) :
    (∑ x, (recOp P F d x)ᴴ * recOp P F d x) * (F y * P) = F y * P := by
  rw [Finset.sum_mul, Finset.sum_eq_single y]
  · rw [recOp_conj hP hd, Matrix.smul_mul,
      show F y * P * (F y)ᴴ * (F y * P) = F y * (P * (F y)ᴴ * F y * P) by noncomm_ring,
      hFF y y, if_pos rfl, Matrix.mul_smul, smul_smul]
    rcases eq_or_lt_of_le (hd y) with h0 | h0
    · rw [hzero y h0.symm]
      simp
    · have : (d y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
      rw [inv_mul_cancel₀ this, one_smul]
  · intro x _ hx
    rw [recOp_conj hP hd, Matrix.smul_mul,
      show F x * P * (F x)ᴴ * (F y * P) = F x * (P * (F x)ᴴ * F y * P) by noncomm_ring,
      hFF x y, if_neg hx]
    simp
  · intro h; exact absurd (Finset.mem_univ y) h

omit [DecidableEq n] in
lemma sandwich (hP : IsCodeProjector P) (B : Matrix n n ℂ) (G : Matrix n n ℂ)
    {rho : Matrix n n ℂ} (hrho : P * rho * P = rho) :
    B * G * rho * Gᴴ * Bᴴ = (B * G * P) * rho * (B * G * P)ᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP.herm]
  conv_lhs => rw [← hrho]
  noncomm_ring

/-- The recovery family is a channel. -/
lemma recFam_sum_one (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P) :
    ∑ k, (recFam P F d k)ᴴ * recFam P F d k = 1 := by
  set Pi : Matrix n n ℂ := ∑ x, (recOp P F d x)ᴴ * recOp P F d x with hPi
  have hherm : Piᴴ = Pi := by
    rw [hPi]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]
  rw [Fintype.sum_option]
  show (1 - Pi)ᴴ * (1 - Pi) + ∑ x, (recOp P F d x)ᴴ * recOp P F d x = 1
  rw [← hPi, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hherm,
    show (1 - Pi) * (1 - Pi) = 1 - Pi - Pi + Pi * Pi by noncomm_ring, pi_idem hP hd hFF, ← hPi]
  noncomm_ring

/-- The recovery family undoes the error channel given in diagonal form. -/
lemma recFam_recovers (hP : IsCodeProjector P) (hd : ∀ x, 0 ≤ d x)
    (hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P)
    (hzero : ∀ x, d x = 0 → F x * P = 0) (hFsum : ∑ y, (F y)ᴴ * F y = 1)
    (rho : Matrix n n ℂ) (hrho : P * rho * P = rho) :
    ∑ k, ∑ y, recFam P F d k * F y * rho * (F y)ᴴ * (recFam P F d k)ᴴ = rho := by
  rw [Fintype.sum_option]
  have hnone : ∑ y, recFam P F d none * F y * rho * (F y)ᴴ * (recFam P F d none)ᴴ = 0 := by
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [sandwich hP _ _ hrho]
    have h0 : recFam P F d none * F y * P = 0 := by
      show (1 - ∑ x, (recOp P F d x)ᴴ * recOp P F d x) * F y * P = 0
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, mul_assoc, pi_mul hP hd hFF hzero y,
        sub_self]
    rw [h0]
    simp
  have hsome : ∀ x : A, ∑ y, recFam P F d (some x) * F y * rho * (F y)ᴴ
      * (recFam P F d (some x))ᴴ = (d x : ℂ) • rho := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [sandwich hP _ _ hrho]
      show (recOp P F d x * F x * P) * rho * (recOp P F d x * F x * P)ᴴ = _
      rw [recOp_mul hd hFF, if_pos rfl, Matrix.conjTranspose_smul, hP.herm, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul, hrho,
        show star ((Real.sqrt (d x) : ℝ) : ℂ) = ((Real.sqrt (d x) : ℝ) : ℂ) by simp]
      congr 1
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd x)]
    · intro y _ hy
      rw [sandwich hP _ _ hrho]
      show (recOp P F d x * F y * P) * rho * (recOp P F d x * F y * P)ᴴ = _
      rw [recOp_mul hd hFF, if_neg hy.symm]
      simp
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hnone, zero_add, Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hsome x,
    ← Finset.sum_smul, sum_d_eq_one hP hFF hFsum, one_smul]

end Diagonal

/-! ### Diagonalizing the Knill–Laflamme matrix -/

omit [Fintype n] [DecidableEq n] in
lemma sum_unitary_comb (U : Matrix A A ℂ) (hU : U * Uᴴ = 1) (G : A → A → Matrix n n ℂ) :
    ∑ y, ∑ b, ∑ b', ((U b y * star (U b' y)) • G b b') = ∑ b, G b b := by
  have step1 : ∑ y, ∑ b, ∑ b', ((U b y * star (U b' y)) • G b b')
      = ∑ b, ∑ b', (∑ y, (U b y * star (U b' y))) • G b b' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [← Finset.sum_smul]
  rw [step1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b]
  · have h : ∑ y, U b y * star (U b y) = 1 := by
      have := congrFun (congrFun hU b) b
      rw [Matrix.mul_apply] at this
      simpa [Matrix.conjTranspose_apply] using this
    rw [h, one_smul]
  · intro b' _ hb'
    have h : ∑ y, U b y * star (U b' y) = 0 := by
      have := congrFun (congrFun hU b) b'
      rw [Matrix.mul_apply] at this
      simpa [Matrix.conjTranspose_apply, Matrix.one_apply, Ne.symm hb'] using this
    rw [h, zero_smul]
  · intro h; exact absurd (Finset.mem_univ b) h

omit [DecidableEq n] in
/-- Two Kraus families related by a unitary matrix define the same channel. -/
lemma kraus_unitary_eq (E : A → Matrix n n ℂ) (U : Matrix A A ℂ) (hU : U * Uᴴ = 1)
    (rho : Matrix n n ℂ) :
    ∑ y, (∑ b, U b y • E b) * rho * (∑ b, U b y • E b)ᴴ = ∑ a, E a * rho * (E a)ᴴ := by
  rw [← sum_unitary_comb U hU (fun b b' => E b * rho * (E b')ᴴ)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  congr 1
  ring

/-- A unitary change of Kraus operators preserves trace preservation. -/
lemma kraus_unitary_sum_one (E : A → Matrix n n ℂ) (U : Matrix A A ℂ) (hU : U * Uᴴ = 1)
    (hE : IsKrausChannel E) :
    ∑ y, (∑ b, U b y • E b)ᴴ * (∑ b, U b y • E b) = 1 := by
  rw [← hE, ← sum_unitary_comb U hU (fun b b' => (E b')ᴴ * E b)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]

omit [DecidableEq n] [DecidableEq A] in
/-- The Knill–Laflamme conditions in the rotated Kraus basis. -/
lemma kl_rotated (P : Matrix n n ℂ) (E : A → Matrix n n ℂ) (c : A → A → ℂ) (U : Matrix A A ℂ)
    (hc : ∀ a b, P * (E a)ᴴ * E b * P = c a b • P) (x y : A) :
    P * (∑ b, U b x • E b)ᴴ * (∑ b, U b y • E b) * P = ((Uᴴ * (Matrix.of c) * U) x y) • P := by
  have h1 : P * (∑ b, U b x • E b)ᴴ * (∑ b, U b y • E b) * P
      = ∑ b, ∑ b', ((star (U b' x) * (c b' b * U b y)) • P : Matrix n n ℂ) := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum,
      Matrix.sum_mul]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [show P * (star (U b' x) • (E b')ᴴ) * (U b y • E b) * P
        = (star (U b' x) * U b y) • (P * (E b')ᴴ * E b * P) by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1
      ring]
    rw [hc b' b, smul_smul]
    congr 1
    ring
  rw [h1]
  simp only [← Finset.sum_smul]
  congr 1
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp [Matrix.conjTranspose_apply]
  ring

omit [DecidableEq n] [Fintype A] [DecidableEq A] in
/-- The matrix of Knill–Laflamme coefficients is Hermitian. -/
lemma kl_isHermitian {P : Matrix n n ℂ} {E : A → Matrix n n ℂ} {c : A → A → ℂ}
    (hP : IsCodeProjector P) (hc : ∀ a b, P * (E a)ᴴ * E b * P = c a b • P) :
    (Matrix.of c).IsHermitian := by
  ext a b
  have h1 : (P * (E b)ᴴ * E a * P)ᴴ = P * (E a)ᴴ * E b * P := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP.herm]
    noncomm_ring
  rw [hc b a, hc a b, Matrix.conjTranspose_smul, hP.herm] at h1
  exact smul_eq_smul_of_ne_zero hP.nontrivial h1

omit [DecidableEq A] in
/-- Any recovery family can be re-indexed by `Fin m`. -/
lemma corrects_of_isRecovery {K : Type*} [Fintype K] {P : Matrix n n ℂ} {E : A → Matrix n n ℂ}
    {R : K → Matrix n n ℂ} (h : IsRecovery P E R) : Corrects P E := by
  refine ⟨Fintype.card K, R ∘ (Fintype.equivFin K).symm, ?_, ?_⟩
  · rw [← h.1]
    exact Equiv.sum_comp (Fintype.equivFin K).symm (fun k => (R k)ᴴ * R k)
  · intro rho hrho
    exact (Equiv.sum_comp (Fintype.equivFin K).symm
      (fun k => ∑ a, R k * E a * rho * (E a)ᴴ * (R k)ᴴ)).trans (h.2 rho hrho)

lemma corrects_of_knill_laflamme (P : Matrix n n ℂ) (E : A → Matrix n n ℂ)
    (hP : IsCodeProjector P) (hE : IsKrausChannel E)
    (h : KnillLaflammeCondition P E) : Corrects P E := by
  obtain ⟨c, hc⟩ := h
  -- diagonalize the Knill–Laflamme matrix
  have hcM : (Matrix.of c).IsHermitian := kl_isHermitian hP hc
  set U : Matrix A A ℂ := (hcM.eigenvectorUnitary : Matrix A A ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := by
    have := hcM.eigenvectorUnitary.2.1
    rw [Matrix.star_eq_conjTranspose] at this
    exact this
  have hU2 : U * Uᴴ = 1 := by
    have := hcM.eigenvectorUnitary.2.2
    rw [Matrix.star_eq_conjTranspose] at this
    exact this
  set d : A → ℝ := hcM.eigenvalues with hddef
  have hdiag : Uᴴ * (Matrix.of c) * U = diagonal (RCLike.ofReal ∘ d) := by
    have := hcM.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hUdef, hddef, Matrix.star_eq_conjTranspose] using this
  set F : A → Matrix n n ℂ := fun y => ∑ b, U b y • E b with hFdef
  have hFF : ∀ x y, P * (F x)ᴴ * F y * P = (if x = y then (d x : ℂ) else 0) • P := by
    intro x y
    rw [hFdef, kl_rotated P E c U hc x y, hdiag, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  have hFsum : ∑ y, (F y)ᴴ * F y = 1 := kraus_unitary_sum_one E U hU2 hE
  have hd : ∀ x, 0 ≤ d x := fun x => d_nonneg hP hFF x
  have hzero : ∀ x, d x = 0 → F x * P = 0 := fun x hx => FP_eq_zero hP hFF hx
  refine corrects_of_isRecovery (K := Option A) (R := recFam P F d) ⟨?_, ?_⟩
  · exact recFam_sum_one hP hd hFF
  · intro rho hrho
    have hstep : ∀ k : Option A, ∑ a, recFam P F d k * E a * rho * (E a)ᴴ * (recFam P F d k)ᴴ
        = ∑ y, recFam P F d k * F y * rho * (F y)ᴴ * (recFam P F d k)ᴴ := by
      intro k
      have hL : ∀ (B : Matrix n n ℂ) (G : A → Matrix n n ℂ),
          ∑ a, B * G a * rho * (G a)ᴴ * Bᴴ = B * (∑ a, G a * rho * (G a)ᴴ) * Bᴴ := by
        intro B G
        rw [Matrix.mul_sum, Matrix.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by noncomm_ring
      rw [hL (recFam P F d k) E, hL (recFam P F d k) F,
        kraus_unitary_eq E U hU2 rho]
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hstep k]
    exact recFam_recovers hP hd hFF hzero hFsum rho hrho

/-- **Knill–Laflamme theorem.**  A code (given by the projector `P` onto the code subspace)
corrects an error set `E` (i.e. there is a recovery channel undoing the error channel on all
states supported by the code) if and only if the Knill–Laflamme conditions
`P Eₐ† E_b P = c a b • P` hold. -/
theorem knill_laflamme (P : Matrix n n ℂ) (E : A → Matrix n n ℂ)
    (hP : IsCodeProjector P) (hE : IsKrausChannel E) :
    Corrects P E ↔ KnillLaflammeCondition P E :=
  ⟨knill_laflamme_of_corrects P E hP, corrects_of_knill_laflamme P E hP hE⟩

/-- Sanity check that the hypotheses of the theorem are satisfiable: the whole space, seen as a
code, corrects the trivial (identity) error. -/
example : Corrects (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine (knill_laflamme _ _ ⟨by simp, by simp, by simp⟩ (by simp [IsKrausChannel])).2
    ⟨fun _ _ => 1, fun a b => by simp⟩

end QI

