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
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of (strictly) positive
eigenvalues.  (For non-Hermitian matrices the value is set to `0`.) -/
noncomputable def posIndex (Q : Matrix n n 𝕜) : ℕ :=
  if h : Q.IsHermitian then (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card else 0

theorem posIndex_eq (Q : Matrix n n 𝕜) (hQ : Q.IsHermitian) :
    posIndex Q = (Finset.univ.filter (fun i => 0 < hQ.eigenvalues i)).card := by
  rw [posIndex, dif_pos hQ]

/-- For a Hermitian matrix `G` there is an orthogonal projection `E` onto the range of `G`:
it is Hermitian, idempotent, acts as the identity on the range of `G`, kills everything
orthogonal to that range, and has trace equal to the rank of `G`. -/
theorem exists_range_proj (G : Matrix n n 𝕜) (hG : G.IsHermitian) :
    ∃ E : Matrix n n 𝕜, Eᴴ = E ∧ E * E = E ∧ E * G = G ∧
      (∀ B : Matrix n n 𝕜, B * G = 0 → B * E = 0) ∧ E.trace = (G.rank : 𝕜) := by
  classical
  set u : Matrix n n 𝕜 := (hG.eigenvectorUnitary : Matrix n n 𝕜) with hudef
  have hu : uᴴ * u = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self hG.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  set L : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hG.eigenvalues) with hL
  have hspec : G = u * L * uᴴ := by
    have := hG.spectral_theorem
    simpa [hudef, hL, Matrix.star_eq_conjTranspose] using this
  set D : Matrix n n 𝕜 := diagonal (fun i => if hG.eigenvalues i ≠ 0 then (1:𝕜) else 0) with hD
  have key : ∀ X : Matrix n n 𝕜, uᴴ * (u * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1; funext i; by_cases h : hG.eigenvalues i ≠ 0 <;> simp [h]
  have hDD : D * D = D := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : hG.eigenvalues i ≠ 0 <;> simp [h]
  have hDL : D * L = L := by
    rw [hD, hL, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    by_cases h : hG.eigenvalues i ≠ 0
    · simp [h]
    · simp only [ne_eq, not_not] at h
      simp [h]
  refine ⟨u * D * uᴴ, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hDh]
  · simp only [Matrix.mul_assoc, key, ← Matrix.mul_assoc D D, hDD]
  · rw [hspec]
    simp only [Matrix.mul_assoc, key, ← Matrix.mul_assoc D L, hDL]
  · intro B hB
    rw [hspec] at hB
    have h1 : B * u * L = 0 := by
      have : (B * (u * L * uᴴ)) * u = 0 := by rw [hB, Matrix.zero_mul]
      simpa [Matrix.mul_assoc, hu] using this
    have h2 : B * u * D = 0 := by
      ext j i
      have hji := congrFun (congrFun h1 j) i
      rw [hL, Matrix.mul_diagonal] at hji
      rw [hD, Matrix.mul_diagonal]
      simp only [Matrix.zero_apply] at hji
      by_cases h : hG.eigenvalues i ≠ 0
      · simp only [h, ne_eq, not_false_eq_true, if_pos, Matrix.zero_apply]
        rcases mul_eq_zero.1 hji with h' | h'
        · simp [h']
        · simp only [Function.comp_apply, RCLike.ofReal_eq_zero] at h'
          exact absurd h' h
      · simp [h]
    calc B * (u * D * uᴴ) = (B * u * D) * uᴴ := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [h2, Matrix.zero_mul]
  · rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, hD, Matrix.trace_diagonal,
      hG.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    simp [Finset.sum_ite, Finset.filter_not]

/-- For a Hermitian matrix `Q` there is an orthogonal projection `R` onto the span of the
eigenvectors with positive eigenvalue: its trace is the positive index of inertia, and `Q`
is negative semidefinite on the orthogonal complement of its range. -/
theorem exists_pos_proj (Q : Matrix n n 𝕜) (hQ : Q.IsHermitian) :
    ∃ R : Matrix n n 𝕜, Rᴴ = R ∧ R * R = R ∧ R.trace = ((posIndex Q : ℕ) : 𝕜) ∧
      (-((1 - R) * Q * (1 - R))).PosSemidef := by
  classical
  set u : Matrix n n 𝕜 := (hQ.eigenvectorUnitary : Matrix n n 𝕜) with hudef
  have hu : uᴴ * u = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self hQ.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  have hu2 : u * uᴴ = 1 := (mul_eq_one_comm_of_card_eq n n 𝕜 rfl).mp hu
  set L : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hQ.eigenvalues) with hL
  have hspec : Q = u * L * uᴴ := by
    have := hQ.spectral_theorem
    simpa [hudef, hL, Matrix.star_eq_conjTranspose] using this
  set D : Matrix n n 𝕜 := diagonal (fun i => if 0 < hQ.eigenvalues i then (1:𝕜) else 0) with hD
  have key : ∀ X : Matrix n n 𝕜, uᴴ * (u * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1; funext i; by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
  have hDD : D * D = D := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
  refine ⟨u * D * uᴴ, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hDh]
  · simp only [Matrix.mul_assoc, key, ← Matrix.mul_assoc D D, hDD]
  · rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, hD, Matrix.trace_diagonal,
      posIndex_eq Q hQ]
    simp
  · have hone : (1 : Matrix n n 𝕜) - u * D * uᴴ = u * (1 - D) * uᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu2]
    rw [hone, hspec]
    have hprod : u * (1 - D) * uᴴ * (u * L * uᴴ) * (u * (1 - D) * uᴴ)
        = u * ((1 - D) * L * (1 - D)) * uᴴ := by
      simp only [Matrix.mul_assoc, key]
    rw [hprod]
    have hone' : (1 : Matrix n n 𝕜) - D = diagonal (fun i =>
        if 0 < hQ.eigenvalues i then (0:𝕜) else 1) := by
      rw [hD]
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
      · simp [hij]
    have hdiag : (1 - D) * L * (1 - D)
        = diagonal (fun i =>
            if 0 < hQ.eigenvalues i then (0:𝕜) else RCLike.ofReal (hQ.eigenvalues i)) := by
      rw [hone', hL, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; funext i; by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
    rw [hdiag]
    have hnegd : -(u * (diagonal (fun i =>
          if 0 < hQ.eigenvalues i then (0:𝕜) else RCLike.ofReal (hQ.eigenvalues i))) * uᴴ)
        = u * (diagonal (fun i =>
          -(if 0 < hQ.eigenvalues i then (0:𝕜) else RCLike.ofReal (hQ.eigenvalues i)))) * uᴴ := by
      rw [← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [hnegd]
    have hpsd : (diagonal (fun i =>
        -(if 0 < hQ.eigenvalues i then (0:𝕜) else RCLike.ofReal (hQ.eigenvalues i)))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      by_cases h : 0 < hQ.eigenvalues i
      · simp [h]
      · simp only [h, if_false]
        push_neg at h
        rw [← RCLike.ofReal_neg]
        exact RCLike.ofReal_nonneg.mpr (by linarith)
    simpa using hpsd.mul_mul_conjTranspose_same u

/-- Rank–trace inequality (preprint Lemma 3.2).  If `P` is positive semidefinite of rank at
most `r`, `Q` is Hermitian with at most `b` positive eigenvalues and `c > 0`, then
`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²`, where `‖M‖_F² = Re tr (Mᴴ M)`. -/
theorem rank_trace_ineq (P Q : Matrix n n 𝕜) (r b : ℕ) (c : ℝ)
    (hP : P.PosSemidef) (hPr : P.rank ≤ r)
    (hQ : Q.IsHermitian) (hQb : posIndex Q ≤ b) (hc : 0 < c) :
    c * RCLike.re P.trace - (c ^ 2 / 4) * r + 2 * c * RCLike.re Q.trace - c ^ 2 * b
      ≤ RCLike.re (((P + Q)ᴴ * (P + Q)).trace) := by
  classical
  -- `R` : the spectral projection onto the positive part of `Q`; `S = 1 - R`.
  obtain ⟨R, hRh, hRR, hRtr, hRneg⟩ := exists_pos_proj Q hQ
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix n n 𝕜, S = 1 - R := ⟨_, rfl⟩
  rw [← hSdef] at hRneg
  have hSh : Sᴴ = S := by rw [hSdef]; simp [hRh]
  have hSS : S * S = S := by
    rw [hSdef]
    have h : ((1 : Matrix n n 𝕜) - R) * (1 - R) = 1 - R - R + R * R := by noncomm_ring
    rw [h, hRR]; abel
  have hRS : R * S = 0 := by
    rw [hSdef]
    have h : R * ((1 : Matrix n n 𝕜) - R) = R - R * R := by noncomm_ring
    rw [h, hRR, sub_self]
  have hSR : S * R = 0 := by
    rw [hSdef]
    have h : ((1 : Matrix n n 𝕜) - R) * R = R - R * R := by noncomm_ring
    rw [h, hRR, sub_self]
  -- `G` : the compression of `P` to the range of `S`
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix n n 𝕜, G = S * P * S := ⟨_, rfl⟩
  have hGpsd : G.PosSemidef := by
    rw [hGdef]
    have := hP.conjTranspose_mul_mul_same S
    rwa [hSh] at this
  obtain ⟨W, hWh, hWW, hWG, hWuniv, hWtr⟩ := exists_range_proj G hGpsd.isHermitian
  have hSG : S * G = G := by
    rw [hGdef]
    calc S * (S * P * S) = S * S * P * S := by simp only [Matrix.mul_assoc]
      _ = S * P * S := by rw [hSS]
  have hSW : S * W = W := by
    have h0 : (S - 1) * G = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hSG, sub_self]
    have h1 := hWuniv _ h0
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  have hWS : W * S = W := by
    have := congrArg Matrix.conjTranspose hSW
    rwa [Matrix.conjTranspose_mul, hWh, hSh] at this
  have hRW : R * W = 0 := by rw [← hSW, ← Matrix.mul_assoc, hRS, Matrix.zero_mul]
  have hWR : W * R = 0 := by rw [← hWS, Matrix.mul_assoc, hSR, Matrix.mul_zero]
  -- `E` : the complementary projection inside the range of `S`
  obtain ⟨E, hEdef⟩ : ∃ E : Matrix n n 𝕜, E = S - W := ⟨_, rfl⟩
  have hEh : Eᴴ = E := by rw [hEdef, Matrix.conjTranspose_sub, hSh, hWh]
  have hEE : E * E = E := by
    rw [hEdef]
    have h : (S - W) * (S - W) = S * S - S * W - W * S + W * W := by noncomm_ring
    rw [h, hSS, hSW, hWS, hWW]; abel
  have hSE : S * E = E := by
    rw [hEdef]
    have h : S * (S - W) = S * S - S * W := by noncomm_ring
    rw [h, hSS, hSW]
  have hES : E * S = E := by
    rw [hEdef]
    have h : (S - W) * S = S * S - W * S := by noncomm_ring
    rw [h, hSS, hWS]
  have hEG : E * G = 0 := by
    rw [hEdef]
    have h : (S - W) * G = S * G - W * G := by noncomm_ring
    rw [h, hSG, hWG, sub_self]
  -- `Q` is negative semidefinite on the range of `S`
  have hgenQ : ∀ F : Matrix n n 𝕜, Fᴴ = F → F * F = F → S * F = F → F * S = F →
      RCLike.re ((Q * F).trace) ≤ 0 := by
    intro F hFh hFF hSF hFS
    have hpsd : (Fᴴ * (-(S * Q * S)) * F).PosSemidef := hRneg.conjTranspose_mul_mul_same F
    have heq : Fᴴ * (-(S * Q * S)) * F = -(F * Q * F) := by
      rw [hFh, Matrix.mul_neg, Matrix.neg_mul]
      congr 1
      calc F * (S * Q * S) * F = (F * S) * Q * (S * F) := by simp only [Matrix.mul_assoc]
        _ = F * Q * F := by rw [hFS, hSF]
    rw [heq] at hpsd
    have h0 : 0 ≤ RCLike.re ((-(F * Q * F)).trace) := (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1
    have h1 : (F * Q * F).trace = (Q * F).trace := by
      rw [Matrix.trace_mul_cycle, hFF, Matrix.trace_mul_comm]
    rw [Matrix.trace_neg, h1, map_neg] at h0
    linarith
  have hQW : RCLike.re ((Q * W).trace) ≤ 0 := hgenQ W hWh hWW hSW hWS
  have hQE : RCLike.re ((Q * E).trace) ≤ 0 := hgenQ E hEh hEE hSE hES
  -- `tr (P W) ≤ tr P`
  have hPW : RCLike.re ((P * W).trace) ≤ RCLike.re P.trace := by
    have hT : ((1 : Matrix n n 𝕜) - W)ᴴ = 1 - W := by
      rw [Matrix.conjTranspose_sub, hWh, Matrix.conjTranspose_one]
    have hTT : ((1 : Matrix n n 𝕜) - W) * (1 - W) = 1 - W := by
      have h : ((1 : Matrix n n 𝕜) - W) * (1 - W) = 1 - W - W + W * W := by noncomm_ring
      rw [h, hWW]; abel
    have hpsd : (((1 : Matrix n n 𝕜) - W)ᴴ * P * (1 - W)).PosSemidef :=
      hP.conjTranspose_mul_mul_same _
    have h0 : 0 ≤ RCLike.re ((((1 : Matrix n n 𝕜) - W)ᴴ * P * (1 - W)).trace) :=
      (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1
    have heq : (((1 : Matrix n n 𝕜) - W)ᴴ * P * (1 - W)).trace = P.trace - (P * W).trace := by
      rw [hT, Matrix.trace_mul_cycle, hTT, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
        Matrix.trace_mul_comm W P]
    rw [heq, map_sub] at h0
    linarith
  -- `tr (P E) = 0`
  have hPE : RCLike.re ((P * E).trace) = 0 := by
    have hzero : E * P * E = 0 := by
      calc E * P * E = (E * S) * P * (S * E) := by rw [hES, hSE]
        _ = (E * G) * E := by rw [hGdef]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hEG, Matrix.zero_mul]
    have heq : (E * P * E).trace = (P * E).trace := by
      rw [Matrix.trace_mul_cycle, hEE, Matrix.trace_mul_comm]
    rw [← heq, hzero, Matrix.trace_zero, map_zero]
  -- the test matrix `X = c R + (c/2) W`
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix n n 𝕜, X = (c : 𝕜) • R + ((c : 𝕜) / 2) • W := ⟨_, rfl⟩
  have hXh : Xᴴ = X := by
    rw [hXdef]
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hRh, hWh, RCLike.star_def,
      RCLike.conj_ofReal]
  have hMh : (P + Q)ᴴ = P + Q := by
    rw [Matrix.conjTranspose_add, hP.1, hQ]
  have hexpand : ((P + Q - X)ᴴ * (P + Q - X)).trace
      = ((P + Q)ᴴ * (P + Q)).trace - (((P + Q) * X).trace + ((P + Q) * X).trace)
        + (X * X).trace := by
    rw [Matrix.conjTranspose_sub, hXh, hMh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm X (P + Q)]
    ring
  have hkey0 : 0 ≤ RCLike.re (((P + Q - X)ᴴ * (P + Q - X)).trace) :=
    (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (P + Q - X)).trace_nonneg).1
  have hMX : ((P + Q) * X).trace
      = (c : 𝕜) * ((P + Q) * R).trace + ((c : 𝕜) / 2) * ((P + Q) * W).trace := by
    rw [hXdef, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul]
    simp [smul_eq_mul]
  have hXX : (X * X).trace
      = ((c : 𝕜) ^ 2) * (posIndex Q : 𝕜) + ((c : 𝕜) ^ 2 / 4) * (G.rank : 𝕜) := by
    have hprod : X * X = ((c : 𝕜) ^ 2) • R + ((c : 𝕜) ^ 2 / 4) • W := by
      rw [hXdef]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hRR, hWW,
        hRW, hWR, smul_zero, smul_smul, add_zero, zero_add]
      congr 1
      · congr 1; ring
      · congr 1; ring
    rw [hprod, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hRtr, hWtr]
    simp [smul_eq_mul]
  -- pass to real parts
  have reMX : RCLike.re (((P + Q) * X).trace)
      = c * RCLike.re (((P + Q) * R).trace) + (c / 2) * RCLike.re (((P + Q) * W).trace) := by
    rw [hMX, map_add, show ((c : 𝕜) / 2) = (((c / 2 : ℝ)) : 𝕜) by push_cast; ring,
      RCLike.re_ofReal_mul, RCLike.re_ofReal_mul]
  have reXX : RCLike.re ((X * X).trace)
      = c ^ 2 * (posIndex Q : ℝ) + (c ^ 2 / 4) * (G.rank : ℝ) := by
    rw [hXX, map_add,
      show ((c : 𝕜) ^ 2) * (posIndex Q : 𝕜) = (((c ^ 2 : ℝ)) : 𝕜) * (posIndex Q : 𝕜) by
        push_cast; ring,
      show ((c : 𝕜) ^ 2 / 4) * (G.rank : 𝕜) = (((c ^ 2 / 4 : ℝ)) : 𝕜) * (G.rank : 𝕜) by
        push_cast; ring,
      RCLike.re_ofReal_mul, RCLike.re_ofReal_mul]
    simp
  have reExpand : RCLike.re (((P + Q - X)ᴴ * (P + Q - X)).trace)
      = RCLike.re (((P + Q)ᴴ * (P + Q)).trace) - 2 * RCLike.re (((P + Q) * X).trace)
        + RCLike.re ((X * X).trace) := by
    rw [hexpand, map_add, map_sub, map_add]
    ring
  -- decomposition of the traces
  have hR1 : R = 1 - W - E := by rw [hEdef, hSdef]; abel
  have hMR : ((P + Q) * R).trace
      = (P + Q).trace - ((P + Q) * W).trace - ((P + Q) * E).trace := by
    have h : (P + Q) * R = (P + Q) - (P + Q) * W - (P + Q) * E := by rw [hR1]; noncomm_ring
    rw [h, Matrix.trace_sub, Matrix.trace_sub]
  have hMWtr : ((P + Q) * W).trace = (P * W).trace + (Q * W).trace := by
    rw [Matrix.add_mul, Matrix.trace_add]
  have hMEtr : ((P + Q) * E).trace = (P * E).trace + (Q * E).trace := by
    rw [Matrix.add_mul, Matrix.trace_add]
  have hMtr : (P + Q).trace = P.trace + Q.trace := Matrix.trace_add P Q
  -- rank and index bounds
  have hGr : (G.rank : ℝ) ≤ (r : ℝ) := by
    have h1 : G.rank ≤ P.rank := by
      rw [hGdef, Matrix.mul_assoc]
      exact le_trans (Matrix.rank_mul_le_right S (P * S)) (Matrix.rank_mul_le_left P S)
    exact_mod_cast le_trans h1 hPr
  have hpi : ((posIndex Q : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hQb
  -- final assembly
  have reMR : RCLike.re (((P + Q) * R).trace)
      = (RCLike.re P.trace + RCLike.re Q.trace) - (RCLike.re ((P * W).trace)
        + RCLike.re ((Q * W).trace)) - (RCLike.re ((P * E).trace) + RCLike.re ((Q * E).trace)) := by
    rw [hMR, map_sub, map_sub, hMWtr, hMEtr, hMtr, map_add, map_add, map_add]
  have reMW : RCLike.re (((P + Q) * W).trace)
      = RCLike.re ((P * W).trace) + RCLike.re ((Q * W).trace) := by
    rw [hMWtr, map_add]
  have hstep1 : RCLike.re P.trace + 2 * RCLike.re Q.trace
      ≤ 2 * RCLike.re (((P + Q) * R).trace) + RCLike.re (((P + Q) * W).trace) := by
    rw [reMR, reMW]; linarith
  have hstep2 : c * (RCLike.re P.trace + 2 * RCLike.re Q.trace)
      ≤ c * (2 * RCLike.re (((P + Q) * R).trace) + RCLike.re (((P + Q) * W).trace)) :=
    mul_le_mul_of_nonneg_left hstep1 (le_of_lt hc)
  have hstep3 : c ^ 2 * ((posIndex Q : ℕ) : ℝ) ≤ c ^ 2 * (b : ℝ) :=
    mul_le_mul_of_nonneg_left hpi (sq_nonneg c)
  have hstep4 : (c ^ 2 / 4) * (G.rank : ℝ) ≤ (c ^ 2 / 4) * (r : ℝ) :=
    mul_le_mul_of_nonneg_left hGr (by positivity)
  rw [reExpand, reMX, reXX] at hkey0
  linarith

end Zeta23Core

#print axioms Zeta23Core.rank_trace_ineq

