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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a matrix. -/
noncomputable def rtr (M : Matrix n n 𝕜) : ℝ := RCLike.re M.trace

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/
noncomputable def frobSq (M : Matrix n n 𝕜) : ℝ := rtr (Mᴴ * M)

/-- The positive index of a Hermitian matrix: the number of (strictly) positive eigenvalues. -/
noncomputable def posIndex {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : ℕ :=
  Fintype.card {i // 0 < hQ.eigenvalues i}

/-! ### Basic facts about `rtr` -/

omit [DecidableEq n] in
lemma rtr_add (A B : Matrix n n 𝕜) : rtr (A + B) = rtr A + rtr B := by
  simp [rtr, Matrix.trace_add]

omit [DecidableEq n] in
lemma rtr_sub (A B : Matrix n n 𝕜) : rtr (A - B) = rtr A - rtr B := by
  simp [rtr, Matrix.trace_sub]

omit [DecidableEq n] in
lemma rtr_smul (c : ℝ) (A : Matrix n n 𝕜) : rtr (c • A) = c * rtr A := by
  simp [rtr, Matrix.trace_smul, RCLike.real_smul_eq_coe_mul, RCLike.mul_re]

omit [DecidableEq n] in
lemma rtr_mul_comm (A B : Matrix n n 𝕜) : rtr (A * B) = rtr (B * A) := by
  rw [rtr, rtr, Matrix.trace_mul_comm]

omit [DecidableEq n] in
lemma rtr_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) : 0 ≤ rtr A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

lemma rtr_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    rtr A = ∑ i, hA.eigenvalues i := by
  rw [rtr, hA.trace_eq_sum_eigenvalues]
  simp

omit [Fintype n] in
lemma isHermitian_smul_real {A : Matrix n n 𝕜} (hA : A.IsHermitian) (c : ℝ) :
    (c • A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul]
  simp [hA.eq]

omit [DecidableEq n] in
lemma hermitian_idem_posSemidef {R : Matrix n n 𝕜} (h : R.IsHermitian) (h2 : R * R = R) :
    R.PosSemidef := by
  have hR : R = Rᴴ * R := by rw [h, h2]
  rw [hR]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ### The functional calculus toolkit -/

section CFC

variable {A : Matrix n n 𝕜}

lemma cfc_eq_conj (hA : A.IsHermitian) (f : ℝ → ℝ) :
    hA.cfc f = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp [Matrix.star_eq_conjTranspose]

lemma eigenvectorUnitary_conjTranspose_mul (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix n n 𝕜))ᴴ * (hA.eigenvectorUnitary : Matrix n n 𝕜) = 1 := by
  have h := hA.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h

lemma conj_mul_conj (hA : A.IsHermitian) (D E : Matrix n n 𝕜) :
    ((hA.eigenvectorUnitary : Matrix n n 𝕜) * D * (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ) *
      ((hA.eigenvectorUnitary : Matrix n n 𝕜) * E * (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ)
      = (hA.eigenvectorUnitary : Matrix n n 𝕜) * (D * E) *
        (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ),
    eigenvectorUnitary_conjTranspose_mul, Matrix.one_mul]

lemma cfc_mul (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f * hA.cfc g = hA.cfc (fun x => f x * g x) := by
  have hd : (fun i => (RCLike.ofReal ∘ f ∘ hA.eigenvalues) i *
        (RCLike.ofReal ∘ g ∘ hA.eigenvalues) i)
      = (RCLike.ofReal ∘ (fun x => f x * g x) ∘ hA.eigenvalues : n → 𝕜) := by
    funext i; simp [Function.comp_def]
  rw [cfc_eq_conj, cfc_eq_conj, cfc_eq_conj, conj_mul_conj, Matrix.diagonal_mul_diagonal, hd]

lemma cfc_congr (hA : A.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) : hA.cfc f = hA.cfc g := by
  have hd : (RCLike.ofReal ∘ f ∘ hA.eigenvalues : n → 𝕜)
      = (RCLike.ofReal ∘ g ∘ hA.eigenvalues : n → 𝕜) := by
    funext i; simp [Function.comp_def, h i]
  rw [cfc_eq_conj, cfc_eq_conj, hd]

lemma cfc_add (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f + hA.cfc g = hA.cfc (fun x => f x + g x) := by
  have hd : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) : Matrix n n 𝕜)
      + diagonal (RCLike.ofReal ∘ g ∘ hA.eigenvalues)
      = diagonal (RCLike.ofReal ∘ (fun x => f x + g x) ∘ hA.eigenvalues) := by
    rw [Matrix.diagonal_add]
    congr 1
    funext i
    simp [Function.comp_def]
  rw [cfc_eq_conj, cfc_eq_conj, cfc_eq_conj, ← Matrix.add_mul, ← Matrix.mul_add, hd]

lemma cfc_isHermitian (hA : A.IsHermitian) (f : ℝ → ℝ) : (hA.cfc f).IsHermitian := by
  have hD : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) : Matrix n n 𝕜)ᴴ
      = diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) := by
    simp [Matrix.diagonal_conjTranspose, Function.comp_def, Pi.star_def]
  unfold Matrix.IsHermitian
  rw [cfc_eq_conj]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]

lemma cfc_posSemidef (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) : (hA.cfc f).PosSemidef := by
  have hd : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) : Matrix n n 𝕜).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa [Function.comp_def] using (RCLike.ofReal_nonneg (K := 𝕜)).mpr (hf i)
  rw [cfc_eq_conj]
  exact hd.mul_mul_conjTranspose_same _

lemma cfc_id (hA : A.IsHermitian) : hA.cfc (fun x => x) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rw [Matrix.IsHermitian.cfc]
  rfl

lemma rtr_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    rtr (hA.cfc f) = ∑ i, f (hA.eigenvalues i) := by
  rw [rtr, cfc_eq_conj, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    eigenvectorUnitary_conjTranspose_mul, Matrix.one_mul, Matrix.trace_diagonal]
  simp [Function.comp_def]

lemma cfc_rank_le (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).rank ≤ Fintype.card {i // f (hA.eigenvalues i) ≠ 0} := by
  rw [cfc_eq_conj]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  refine le_trans (Matrix.rank_mul_le_right _ _) ?_
  rw [Matrix.rank_diagonal]
  exact le_of_eq (Fintype.card_congr (Equiv.subtypeEquivRight (by
    intro _
    simp [Function.comp_def])))

end CFC

/-! ### Square roots and positivity of traces -/

/-- The positive semidefinite square root, built from the functional calculus. -/
noncomputable def psdSqrt {A : Matrix n n 𝕜} (hA : A.PosSemidef) : Matrix n n 𝕜 :=
  hA.isHermitian.cfc Real.sqrt

lemma psdSqrt_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) : (psdSqrt hA).PosSemidef :=
  cfc_posSemidef _ fun _ => Real.sqrt_nonneg _

lemma psdSqrt_mul_self {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    psdSqrt hA * psdSqrt hA = A := by
  rw [psdSqrt, cfc_mul, cfc_congr hA.isHermitian (g := fun x => x)
    (fun i => Real.mul_self_sqrt (hA.eigenvalues_nonneg i)), cfc_id]

/-- The trace of a product of two positive semidefinite matrices is nonnegative. -/
lemma rtr_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ rtr (A * B) := by
  have hs := psdSqrt_mul_self hA
  have hh : (psdSqrt hA).IsHermitian := (psdSqrt_posSemidef hA).isHermitian
  have key : (psdSqrt hA * B * (psdSqrt hA)ᴴ).PosSemidef := hB.mul_mul_conjTranspose_same _
  have h3 : (psdSqrt hA * B * (psdSqrt hA)ᴴ).trace = (A * B).trace := by
    rw [hh, Matrix.trace_mul_comm (psdSqrt hA * B) (psdSqrt hA), ← Matrix.mul_assoc, hs]
  have h4 := rtr_nonneg key
  rwa [rtr, h3, ← rtr] at h4

/-- A positive semidefinite matrix with vanishing trace is zero. -/
lemma posSemidef_eq_zero_of_rtr_eq_zero {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : rtr A = 0) : A = 0 := by
  rw [rtr_eq_sum_eigenvalues hA.isHermitian] at h
  refine hA.isHermitian.eigenvalues_eq_zero_iff.mp (funext fun i => ?_)
  refine le_antisymm ?_ (hA.eigenvalues_nonneg i)
  exact (Finset.single_le_sum (f := hA.isHermitian.eigenvalues)
    (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)).trans h.le

lemma eq_zero_of_add_eq_zero {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : A + B = 0) : A = 0 := by
  refine posSemidef_eq_zero_of_rtr_eq_zero hA (le_antisymm ?_ (rtr_nonneg hA))
  have h0 : rtr A + rtr B = 0 := by
    rw [← rtr_add, h]
    simp [rtr]
  linarith [rtr_nonneg hB]

/-- If `T` is positive semidefinite and `Kᴴ T K = 0` then `T K = 0`. -/
lemma posSemidef_mul_eq_zero {T K : Matrix n n 𝕜} (hT : T.PosSemidef)
    (h : Kᴴ * T * K = 0) : T * K = 0 := by
  have hh : (psdSqrt hT).IsHermitian := (psdSqrt_posSemidef hT).isHermitian
  have hzero : (psdSqrt hT * K)ᴴ * (psdSqrt hT * K) = 0 := by
    rw [Matrix.conjTranspose_mul, hh, Matrix.mul_assoc, ← Matrix.mul_assoc (psdSqrt hT),
      psdSqrt_mul_self, ← Matrix.mul_assoc, h]
  have h0 : psdSqrt hT * K = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  rw [← psdSqrt_mul_self hT, Matrix.mul_assoc, h0, Matrix.mul_zero]

/-! ### Generic linear algebra helpers -/

omit [DecidableEq n] in
lemma rank_add_le (A B : Matrix n n 𝕜) : (A + B).rank ≤ A.rank + B.rank := by
  have hsub : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rw [Matrix.mulVecLin_add]
    exact LinearMap.range_add_le _ _
  calc (A + B).rank ≤ Module.finrank 𝕜
        (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule 𝕜 (n → 𝕜)) :=
        Submodule.finrank_mono hsub
    _ ≤ A.rank + B.rank := Submodule.finrank_add_le_finrank_add_finrank _ _

/-! ### The core inequality -/

omit [DecidableEq n] in
lemma frobSq_lower {M X : Matrix n n 𝕜} (hM : M.IsHermitian) (hX : X.IsHermitian) :
    2 * rtr (M * X) - rtr (X * X) ≤ frobSq M := by
  have h0 : 0 ≤ frobSq (M - X) := rtr_nonneg (Matrix.posSemidef_conjTranspose_mul_self _)
  have h1 : frobSq (M - X) = rtr ((M - X) * (M - X)) := by
    rw [frobSq, Matrix.conjTranspose_sub, hM, hX]
  have h2 : frobSq M = rtr (M * M) := by rw [frobSq, hM]
  rw [h1, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, rtr_sub, rtr_sub, rtr_sub] at h0
  rw [rtr_mul_comm X M] at h0
  linarith [h2]

/-- The core estimate, stated in terms of abstract projections `Pi` (onto the positive spectral
subspace of `Q`) and `R` (onto the range of `P + Pi`), and the negative part `Qm` of `Q`. -/
lemma key_ineq {P Q Pi R Qm : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hPi : Pi.PosSemidef) (hPi2 : Pi * Pi = Pi)
    (hQm : Qm.PosSemidef) (hQPi : Q * Pi = Q + Qm)
    (hRH : R.IsHermitian) (hR2 : R * R = R)
    (hPR : P * R = P) (hPiR : Pi * R = Pi) (hRPi : R * Pi = Pi)
    {c : ℝ} (hc : 0 ≤ c) :
    c * rtr P + 2 * c * rtr Q - c ^ 2 / 4 * (rtr R + 3 * rtr Pi) ≤ frobSq (P + Q) := by
  set M : Matrix n n 𝕜 := P + Q with hM
  have hMH : M.IsHermitian := hP.isHermitian.add hQ
  set X : Matrix n n 𝕜 := (c / 2) • (R + Pi) with hXdef
  have hXH : X.IsHermitian := isHermitian_smul_real (hRH.add hPi.isHermitian) _
  have hXX : X * X = (c ^ 2 / 4) • (R + Pi + Pi + Pi) := by
    rw [hXdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, hR2, hPi2, hRPi, hPiR, show c / 2 * (c / 2) = c ^ 2 / 4 by ring]
    congr 1
    abel
  have hrXX : rtr (X * X) = c ^ 2 / 4 * (rtr R + 3 * rtr Pi) := by
    rw [hXX, rtr_smul, rtr_add, rtr_add, rtr_add]
    ring
  have hMR : M * R = P + Q * R := by rw [hM, Matrix.add_mul, hPR]
  have hQeq : Q = Q * Pi - Qm := by rw [hQPi]; abel
  have hQR : Q * R = Q + Qm - Qm * R := by
    conv_lhs => rw [hQeq]
    rw [Matrix.sub_mul, Matrix.mul_assoc, hPiR, hQPi]
  have hOneR : ((1 : Matrix n n 𝕜) - R).PosSemidef := by
    refine hermitian_idem_posSemidef (Matrix.isHermitian_one.sub hRH) ?_
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hR2]
    simp
  have hQmR : 0 ≤ rtr Qm - rtr (Qm * R) := by
    have h := rtr_mul_nonneg hQm hOneR
    rw [Matrix.mul_sub, Matrix.mul_one, rtr_sub] at h
    linarith
  have h1 : rtr P + rtr Q ≤ rtr (M * R) := by
    rw [hMR, rtr_add, hQR, rtr_sub, rtr_add]
    linarith
  have hMPi : M * Pi = P * Pi + (Q + Qm) := by rw [hM, Matrix.add_mul, hQPi]
  have h2 : rtr Q ≤ rtr (M * Pi) := by
    rw [hMPi, rtr_add, rtr_add]
    have ha := rtr_mul_nonneg hP hPi
    have hb := rtr_nonneg hQm
    linarith
  have hMX : rtr (M * X) = c / 2 * (rtr (M * R) + rtr (M * Pi)) := by
    rw [hXdef, Matrix.mul_smul, Matrix.mul_add, rtr_smul, rtr_add]
  have hkey := frobSq_lower hMH hXH
  rw [hrXX, hMX] at hkey
  have hmul : c * (rtr P + rtr Q + rtr Q) ≤ c * (rtr (M * R) + rtr (M * Pi)) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  linarith [hkey, hmul]

/-! ### Main theorem -/

/-- **Rank–trace inequality** (Lemma 3.2).  If `P` is positive semidefinite with rank at most `r`,
`Q` is Hermitian with at most `b` positive eigenvalues, and `c > 0`, then
`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²`. -/
theorem rank_trace_ineq {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtr P - c ^ 2 / 4 * r + 2 * c * rtr Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  classical
  -- the spectral projection onto the positive part of `Q`
  set ind : ℝ → ℝ := fun x => if 0 < x then 1 else 0 with hind
  set neg : ℝ → ℝ := fun x => if 0 < x then 0 else -x with hneg
  set Pi : Matrix n n 𝕜 := hQ.cfc ind with hPidef
  set Qm : Matrix n n 𝕜 := hQ.cfc neg with hQmdef
  have hPi : Pi.PosSemidef := by
    refine cfc_posSemidef hQ (fun i => ?_)
    rw [hind]
    dsimp only
    split <;> norm_num
  have hQm : Qm.PosSemidef := by
    refine cfc_posSemidef hQ (fun i => ?_)
    rw [hneg]
    dsimp only
    split
    · exact le_rfl
    · rename_i h
      linarith [not_lt.mp h]
  have hPi2 : Pi * Pi = Pi := by
    rw [hPidef, cfc_mul]
    refine cfc_congr hQ (fun i => ?_)
    rw [hind]
    dsimp only
    split <;> norm_num
  have hQcfc : Q = hQ.cfc (fun x => x) := (cfc_id hQ).symm
  have hQPi : Q * Pi = Q + Qm := by
    calc Q * Pi = hQ.cfc (fun x => x) * hQ.cfc ind := by rw [← hQcfc]
      _ = hQ.cfc (fun x => x * ind x) := cfc_mul hQ _ _
      _ = hQ.cfc (fun x => x + neg x) := by
          refine cfc_congr hQ (fun i => ?_)
          rw [hind, hneg]
          dsimp only
          split <;> ring
      _ = hQ.cfc (fun x => x) + hQ.cfc neg := (cfc_add hQ _ _).symm
      _ = Q + Qm := by rw [← hQcfc]
  -- the projection onto the range of `S = P + Pi`
  set S : Matrix n n 𝕜 := P + Pi with hSdef
  have hS : S.PosSemidef := hP.add hPi
  set ind0 : ℝ → ℝ := fun x => if x = 0 then 0 else 1 with hind0
  set R : Matrix n n 𝕜 := hS.isHermitian.cfc ind0 with hRdef
  have hRH : R.IsHermitian := cfc_isHermitian _ _
  have hR2 : R * R = R := by
    rw [hRdef, cfc_mul]
    refine cfc_congr hS.isHermitian (fun i => ?_)
    rw [hind0]
    dsimp only
    split <;> norm_num
  have hScfc : S = hS.isHermitian.cfc (fun x => x) := (cfc_id hS.isHermitian).symm
  have hRS : R * S = S := by
    calc R * S = hS.isHermitian.cfc ind0 * hS.isHermitian.cfc (fun x => x) := by rw [← hScfc]
      _ = hS.isHermitian.cfc (fun x => ind0 x * x) := cfc_mul _ _ _
      _ = hS.isHermitian.cfc (fun x => x) := by
          refine cfc_congr hS.isHermitian (fun i => ?_)
          rw [hind0]
          dsimp only
          split
          · simp [*]
          · ring
      _ = S := cfc_id _
  -- both `P` and `Pi` are absorbed by `R`
  have hSK : ((1 : Matrix n n 𝕜) - R)ᴴ * S * ((1 : Matrix n n 𝕜) - R) = 0 := by
    have h1 : ((1 : Matrix n n 𝕜) - R)ᴴ = 1 - R := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hRH]
    rw [h1, Matrix.sub_mul, Matrix.one_mul, hRS, sub_self, Matrix.zero_mul]
  have hsplit : ((1 : Matrix n n 𝕜) - R)ᴴ * P * ((1 : Matrix n n 𝕜) - R)
      + ((1 : Matrix n n 𝕜) - R)ᴴ * Pi * ((1 : Matrix n n 𝕜) - R) = 0 := by
    rw [← hSK, hSdef]
    simp [Matrix.mul_add, Matrix.add_mul]
  have hPzero : ((1 : Matrix n n 𝕜) - R)ᴴ * P * ((1 : Matrix n n 𝕜) - R) = 0 :=
    eq_zero_of_add_eq_zero (hP.conjTranspose_mul_mul_same _) (hPi.conjTranspose_mul_mul_same _)
      hsplit
  have hPizero : ((1 : Matrix n n 𝕜) - R)ᴴ * Pi * ((1 : Matrix n n 𝕜) - R) = 0 := by
    rw [hPzero, zero_add] at hsplit
    exact hsplit
  have hPR : P * R = P := by
    have h := posSemidef_mul_eq_zero hP hPzero
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    exact (sub_eq_zero.mp h).symm
  have hPiR : Pi * R = Pi := by
    have h := posSemidef_mul_eq_zero hPi hPizero
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    exact (sub_eq_zero.mp h).symm
  have hRPi : R * Pi = Pi := by
    have h := congrArg Matrix.conjTranspose hPiR
    rw [Matrix.conjTranspose_mul, hRH, hPi.isHermitian] at h
    exact h
  -- trace bounds
  have hrPi : rtr Pi = (posIndex hQ : ℝ) := by
    rw [hPidef, rtr_cfc, posIndex, Fintype.card_subtype]
    rw [hind]
    simp [Finset.sum_boole]
  have hrankPi : Pi.rank ≤ posIndex hQ := by
    refine le_trans (cfc_rank_le hQ ind) (le_of_eq ?_)
    rw [posIndex]
    refine Fintype.card_congr (Equiv.subtypeEquivRight (fun i => ?_))
    rw [hind]
    dsimp only
    constructor
    · intro h
      by_contra hcon
      simp [hcon] at h
    · intro h
      simp [h]
  have hrR : rtr R = (S.rank : ℝ) := by
    rw [hRdef, rtr_cfc, hS.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    rw [hind0]
    simp [Finset.sum_boole, Finset.filter_congr_decidable]
  have hrankS : S.rank ≤ r + b :=
    le_trans (rank_add_le P Pi) (Nat.add_le_add hr (le_trans hrankPi hb))
  -- combine
  have hmain := key_ineq hP hQ hPi hPi2 hQm hQPi hRH hR2 hPR hPiR hRPi hc.le
  have hrRle : rtr R ≤ (r : ℝ) + (b : ℝ) := by
    rw [hrR]
    exact_mod_cast hrankS
  have hrPile : rtr Pi ≤ (b : ℝ) := by
    rw [hrPi]
    exact_mod_cast hb
  have hrPinn : 0 ≤ rtr Pi := rtr_nonneg hPi
  nlinarith [hmain, hrRle, hrPile, hrPinn, sq_nonneg c, hc.le]

end Zeta23Core

