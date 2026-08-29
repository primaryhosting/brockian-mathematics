import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace. -/
noncomputable def rtrace (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (X.trace).re

/-- The squared Frobenius norm, `Re tr (Xᴴ X)`. -/
noncomputable def frobSq (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := ((Xᴴ * X).trace).re

/-- The real Frobenius inner product `Re tr (Xᴴ Y)`. -/
noncomputable def fip (X Y : Matrix (Fin d) (Fin d) ℂ) : ℝ := ((Xᴴ * Y).trace).re

/-- The number of strictly positive eigenvalues of a Hermitian matrix
(the *positive index of inertia*); `0` by convention for non-Hermitian matrices. -/
noncomputable def posIndex (Q : Matrix (Fin d) (Fin d) ℂ) : ℕ :=
  if h : Q.IsHermitian then (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card else 0

lemma rtrace_eq_sum_diag (X : Matrix (Fin d) (Fin d) ℂ) : rtrace X = ∑ i, (X i i).re := by
  simp [rtrace, Matrix.trace, Matrix.diag, Complex.re_sum]

lemma rtrace_zero : rtrace (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by simp [rtrace]

lemma frobSq_eq_sum (X : Matrix (Fin d) (Fin d) ℂ) :
    frobSq X = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  simp

lemma frobSq_nonneg (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ frobSq X := by
  rw [frobSq_eq_sum]; positivity

lemma frobSq_zero : frobSq (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by simp [frobSq]

lemma sum_diag_sq_le_frobSq (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, ‖X i i‖ ^ 2 ≤ frobSq X := by
  rw [frobSq_eq_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j => ‖X i j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)

/-! ## The Frobenius inner product -/

lemma fip_self (X : Matrix (Fin d) (Fin d) ℂ) : fip X X = frobSq X := rfl

lemma fip_symm (X Y : Matrix (Fin d) (Fin d) ℂ) : fip X Y = fip Y X := by
  unfold fip
  have h : (Yᴴ * X) = (Xᴴ * Y)ᴴ := by simp [Matrix.conjTranspose_mul]
  rw [h, Matrix.trace_conjTranspose]
  simp

lemma fip_add_left (X Y Z : Matrix (Fin d) (Fin d) ℂ) :
    fip (X + Y) Z = fip X Z + fip Y Z := by
  simp [fip, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]

lemma fip_of_isHermitian {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) :
    fip X Y = rtrace (X * Y) := by
  unfold fip rtrace; rw [hX]

lemma frobSq_add (X Y : Matrix (Fin d) (Fin d) ℂ) :
    frobSq (X + Y) = frobSq X + frobSq Y + 2 * fip X Y := by
  rw [← fip_self, fip_add_left]
  unfold fip frobSq
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rw [show ((Yᴴ * X).trace).re = ((Xᴴ * Y).trace).re from fip_symm Y X]
  ring

lemma frobSq_sub (X Y : Matrix (Fin d) (Fin d) ℂ) :
    frobSq (X - Y) = frobSq X + frobSq Y - 2 * fip X Y := by
  rw [sub_eq_add_neg, frobSq_add]
  have h1 : frobSq (-Y) = frobSq Y := by simp [frobSq]
  have h2 : fip X (-Y) = -fip X Y := by simp [fip]
  rw [h1, h2]; ring

/-! ## Unitary invariance -/

lemma trace_conj {U X : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) :
    (U * X * Uᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

lemma conj_mul_conj {U X : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) :
    (U * X * Uᴴ)ᴴ * (U * X * Uᴴ) = U * (Xᴴ * X) * Uᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [show Xᴴ * (Uᴴ * (U * (X * Uᴴ))) = Xᴴ * ((Uᴴ * U) * (X * Uᴴ)) by
    simp only [Matrix.mul_assoc]]
  rw [hU, Matrix.one_mul]

lemma rtrace_conj {U X : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) :
    rtrace (U * X * Uᴴ) = rtrace X := by
  unfold rtrace; rw [trace_conj hU]

lemma frobSq_conj {U X : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) :
    frobSq (U * X * Uᴴ) = frobSq X := by
  unfold frobSq; rw [conj_mul_conj hU, trace_conj hU]

lemma rtrace_diagonal (m : Fin d → ℝ) :
    rtrace (Matrix.diagonal (fun i => (m i : ℂ))) = ∑ i, m i := by
  simp [rtrace, Matrix.trace_diagonal, Complex.re_sum]

lemma frobSq_diagonal (m : Fin d → ℝ) :
    frobSq (Matrix.diagonal (fun i => (m i : ℂ))) = ∑ i, (m i) ^ 2 := by
  rw [frobSq_eq_sum]
  simp [Matrix.diagonal_apply, apply_ite]

lemma rtrace_diag_mul (m : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (Matrix.diagonal (fun i => (m i : ℂ)) * W) = ∑ i, m i * (W i i).re := by
  rw [rtrace_eq_sum_diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diagonal_mul]; simp

lemma rtrace_mul_of_decomp {U P N : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (m : Fin d → ℝ) (hP : P = U * Matrix.diagonal (fun i => (m i : ℂ)) * Uᴴ) :
    rtrace (P * N) = ∑ i, m i * ((Uᴴ * N * U) i i).re := by
  have h : P * N = U * (Matrix.diagonal (fun i => (m i : ℂ)) * (Uᴴ * N * U)) * Uᴴ := by
    rw [hP]; simp only [Matrix.mul_assoc, hU', Matrix.mul_one]
  rw [h, rtrace_conj hU, rtrace_diag_mul]

lemma diagonal_sub_diagonal (f g q : Fin d → ℝ) (hfg : ∀ i, f i - g i = q i) :
    Matrix.diagonal (fun i => (f i : ℂ)) - Matrix.diagonal (fun i => (g i : ℂ))
      = Matrix.diagonal (fun i => (q i : ℂ)) := by
  ext i j
  by_cases h : i = j <;> simp [h, ← Complex.ofReal_sub, hfg]

lemma conj_sub_conj (U : Matrix (Fin d) (Fin d) ℂ) (f g q : Fin d → ℝ)
    (hfg : ∀ i, f i - g i = q i) :
    U * Matrix.diagonal (fun i => (f i : ℂ)) * Uᴴ - U * Matrix.diagonal (fun i => (g i : ℂ)) * Uᴴ
      = U * Matrix.diagonal (fun i => (q i : ℂ)) * Uᴴ := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub_diagonal f g q hfg]

lemma conj_mul_conj_eq_zero {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) (f g : Fin d → ℝ)
    (hfg : ∀ i, f i * g i = 0) :
    (U * Matrix.diagonal (fun i => (f i : ℂ)) * Uᴴ) *
      (U * Matrix.diagonal (fun i => (g i : ℂ)) * Uᴴ) = 0 := by
  have h : (U * Matrix.diagonal (fun i => (f i : ℂ)) * Uᴴ) *
      (U * Matrix.diagonal (fun i => (g i : ℂ)) * Uᴴ)
      = U * (Matrix.diagonal (fun i => (f i : ℂ)) * ((Uᴴ * U) *
        Matrix.diagonal (fun i => (g i : ℂ)))) * Uᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, hU, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
  have hz : (fun i => (f i : ℂ) * (g i : ℂ)) = fun _ => (0 : ℂ) := by
    funext i; rw [← Complex.ofReal_mul, hfg i]; simp
  rw [hz]
  simp

/-- Spectral theorem, in the explicit form `A = U D Uᴴ`. -/
lemma hermitian_decomp {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ),
    Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2,
    Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]

/-! ## Positive semidefinite auxiliaries -/

lemma psd_diag_re_nonneg {W : Matrix (Fin d) (Fin d) ℂ} (hW : W.PosSemidef) (i : Fin d) :
    0 ≤ (W i i).re := (Complex.le_def.mp hW.diag_nonneg).1

lemma psd_diag_norm {W : Matrix (Fin d) (Fin d) ℂ} (hW : W.PosSemidef) (i : Fin d) :
    ‖W i i‖ = (W i i).re := by
  have him : (W i i).im = 0 := ((Complex.le_def.mp hW.diag_nonneg).2).symm
  have hre : 0 ≤ (W i i).re := psd_diag_re_nonneg hW i
  rw [← Complex.abs_re_eq_norm.mpr him, abs_of_nonneg hre]

/-! ## The scalar inequality -/

/-- The elementary scalar estimate underlying the rank-trace inequality. -/
lemma scalar_key (p w : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    {k : ℕ} (hk : (Finset.univ.filter (fun i => p i ≠ 0)).card ≤ k) {c : ℝ} (hc : 0 ≤ c) :
    c * (∑ i, p i) - (c ^ 2 / 4) * k + 2 * (∑ i, p i * w i)
      ≤ (∑ i, (p i) ^ 2) + (∑ i, (w i) ^ 2) + c * (∑ i, w i) := by
  have key : ∀ i ∈ Finset.univ, c * p i + 2 * (p i * w i) - ((p i) ^ 2 + (w i) ^ 2 + c * w i)
      ≤ (if p i ≠ 0 then c ^ 2 / 4 else 0) := by
    intro i _
    by_cases h : p i = 0
    · simp only [h, ne_eq, not_true_eq_false, ite_false]
      nlinarith [hw i, sq_nonneg (w i)]
    · rw [if_pos h]
      nlinarith [sq_nonneg (w i - p i + c / 2)]
  have hsum := Finset.sum_le_sum key
  have h2 : ∑ i : Fin d, (if p i ≠ 0 then c ^ 2 / 4 else 0)
      = (c ^ 2 / 4) * (Finset.univ.filter (fun i => p i ≠ 0)).card := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp [mul_comm]
  have h3 : (c ^ 2 / 4) * ((Finset.univ.filter (fun i => p i ≠ 0)).card : ℝ) ≤ (c ^ 2 / 4) * k := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast hk
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [h2] at hsum
  linarith

/-! ## The key matrix estimate -/

/-- If `P = U diag m Uᴴ` is positive semidefinite with at most `k` nonzero eigenvalues and `N` is
positive semidefinite, then the linear part of `P` is controlled by the Frobenius norms, with an
interaction term `2 tr (P N)` on the left. -/
lemma key_decomp {U P N : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (m : Fin d → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hP : P = U * Matrix.diagonal (fun i => (m i : ℂ)) * Uᴴ)
    {k : ℕ} (hk : (Finset.univ.filter (fun i => m i ≠ 0)).card ≤ k)
    (hN : N.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    c * rtrace P - (c ^ 2 / 4) * k + 2 * rtrace (P * N)
      ≤ frobSq P + frobSq N + c * rtrace N := by
  have hUH : (Uᴴ)ᴴ * Uᴴ = 1 := by simpa using hU'
  set W : Matrix (Fin d) (Fin d) ℂ := Uᴴ * N * U with hWdef
  have hWpsd : W.PosSemidef := by
    have h := hN.mul_mul_conjTranspose_same (Uᴴ)
    rw [hWdef]
    simpa using h
  set w : Fin d → ℝ := fun i => (W i i).re with hwdef
  have hw : ∀ i, 0 ≤ w i := fun i => psd_diag_re_nonneg hWpsd i
  have h1 : rtrace P = ∑ i, m i := by rw [hP, rtrace_conj hU, rtrace_diagonal]
  have h2 : frobSq P = ∑ i, (m i) ^ 2 := by rw [hP, frobSq_conj hU, frobSq_diagonal]
  have h3 : rtrace (P * N) = ∑ i, m i * w i := rtrace_mul_of_decomp hU hU' m hP
  have hWN : Uᴴ * N * (Uᴴ)ᴴ = W := by rw [hWdef]; simp
  have h4 : rtrace N = ∑ i, w i := by
    have h := rtrace_conj (U := Uᴴ) (X := N) hUH
    rw [hWN] at h
    rw [← h, rtrace_eq_sum_diag]
  have h5 : ∑ i, (w i) ^ 2 ≤ frobSq N := by
    have hfrob : frobSq W = frobSq N := by
      have h := frobSq_conj (U := Uᴴ) (X := N) hUH
      rw [hWN] at h
      exact h
    calc ∑ i, (w i) ^ 2 = ∑ i, ‖W i i‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [psd_diag_norm hWpsd i]
      _ ≤ frobSq W := sum_diag_sq_le_frobSq W
      _ = frobSq N := hfrob
  have hs := scalar_key m w hm hw hk hc
  rw [h1, h2, h3, h4]
  linarith

/-- Positive semidefinite matrices have nonnegative trace pairing. -/
lemma rtrace_mul_nonneg {P N : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ rtrace (P * N) := by
  obtain ⟨U, hU, hU', hPd⟩ := hermitian_decomp hP.1
  rw [rtrace_mul_of_decomp hU hU' _ hPd]
  refine Finset.sum_nonneg fun i _ => ?_
  have hWpsd : (Uᴴ * N * U).PosSemidef := by
    have h := hN.mul_mul_conjTranspose_same (Uᴴ)
    simpa using h
  exact mul_nonneg (hP.eigenvalues_nonneg i) (psd_diag_re_nonneg hWpsd i)

/-! ## The rank-trace inequality -/

/-- **Rank-trace inequality** (Lemma 3.2).  Let `P` be positive semidefinite with rank at most `r`,
and let `Q` be Hermitian with at most `b` strictly positive eigenvalues.  Then for every `c > 0`,
`c ⬝ tr P - (c²/4) r + 2c ⬝ tr Q - c² b ≤ ‖P + Q‖_F²`. -/
theorem rank_trace_ineq {d r b : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) (hr : P.rank ≤ r) (hb : posIndex Q ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - (c ^ 2 / 4) * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  classical
  -- spectral data of `Q`
  obtain ⟨U, hU, hU', hQd⟩ := hermitian_decomp hQ
  set q : Fin d → ℝ := hQ.eigenvalues with hqdef
  set f : Fin d → ℝ := fun i => max (q i) 0 with hfdef
  set g : Fin d → ℝ := fun i => max (-(q i)) 0 with hgdef
  set R : Matrix (Fin d) (Fin d) ℂ := U * Matrix.diagonal (fun i => (f i : ℂ)) * Uᴴ with hRdef
  set N : Matrix (Fin d) (Fin d) ℂ := U * Matrix.diagonal (fun i => (g i : ℂ)) * Uᴴ with hNdef
  have hfnn : ∀ i, 0 ≤ f i := fun i => le_max_right _ _
  have hgnn : ∀ i, 0 ≤ g i := fun i => le_max_right _ _
  have hRpsd : R.PosSemidef := by
    have h := (Matrix.PosSemidef.diagonal (d := fun i => (f i : ℂ))
      (fun i => by simpa using Complex.zero_le_real.mpr (hfnn i))).mul_mul_conjTranspose_same U
    rw [hRdef]; simpa using h
  have hNpsd : N.PosSemidef := by
    have h := (Matrix.PosSemidef.diagonal (d := fun i => (g i : ℂ))
      (fun i => by simpa using Complex.zero_le_real.mpr (hgnn i))).mul_mul_conjTranspose_same U
    rw [hNdef]; simpa using h
  -- `Q = R - N`
  have hfg_sub : ∀ i, f i - g i = q i := by
    intro i
    simp only [hfdef, hgdef]
    rcases le_or_gt 0 (q i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -(q i) ≤ (0:ℝ))]; ring
    · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith : (0:ℝ) ≤ -(q i))]; ring
  have hQRN : Q = R - N := by
    rw [hRdef, hNdef, conj_sub_conj U f g q hfg_sub]
    exact hQd
  -- `R N = 0`
  have hfg_mul : ∀ i, f i * g i = 0 := by
    intro i
    simp only [hfdef, hgdef]
    rcases le_or_gt 0 (q i) with h | h
    · rw [max_eq_right (by linarith : -(q i) ≤ (0:ℝ))]; ring
    · rw [max_eq_right (le_of_lt h)]; ring
  have hRN : R * N = 0 := by
    rw [hRdef, hNdef]; exact conj_mul_conj_eq_zero hU f g hfg_mul
  -- counting the positive eigenvalues
  have hcount : (Finset.univ.filter (fun i => f i ≠ 0)).card ≤ b := by
    have hfilter : (Finset.univ.filter (fun i => f i ≠ 0))
        = (Finset.univ.filter (fun i => 0 < q i)) := by
      refine Finset.filter_congr fun i _ => ?_
      simp only [hfdef, ne_eq]
      constructor
      · intro h
        rcases le_or_gt (q i) 0 with h' | h'
        · exact absurd (max_eq_right h') h
        · exact h'
      · intro h h0
        rw [max_eq_left (le_of_lt h)] at h0
        exact absurd h0 (ne_of_gt h)
    rw [hfilter]
    have hpi : posIndex Q = (Finset.univ.filter (fun i => 0 < q i)).card := by
      rw [posIndex, dif_pos hQ]
    rw [← hpi]
    exact hb
  -- rank bound for `P`
  have hrank : (Finset.univ.filter (fun i => hP.1.eigenvalues i ≠ 0)).card ≤ r := by
    rw [hP.1.rank_eq_card_non_zero_eigs] at hr
    simpa [Fintype.card_subtype] using hr
  obtain ⟨V, hV, hV', hPd⟩ := hermitian_decomp hP.1
  -- the two applications of the key estimate
  have keyP := key_decomp hV hV' _ (fun i => hP.eigenvalues_nonneg i) hPd hrank hNpsd (le_of_lt hc)
  have keyR : 2 * c * rtrace R - c ^ 2 * b ≤ frobSq R := by
    have h := key_decomp hU hU' f hfnn hRdef hcount (Matrix.PosSemidef.zero) (by linarith : (0:ℝ) ≤ 2 * c)
    simp only [Matrix.mul_zero, rtrace_zero, frobSq_zero, mul_zero, add_zero] at h
    have : (2 * c) ^ 2 / 4 = c ^ 2 := by ring
    rw [this] at h
    linarith
  -- expansion of the Frobenius norm
  have hexp : frobSq (P + Q) = frobSq P + frobSq R + frobSq N
      + 2 * rtrace (P * R) - 2 * rtrace (P * N) - 2 * rtrace (R * N) := by
    have hsplit : P + Q = (P + R) - N := by rw [hQRN]; abel
    rw [hsplit, frobSq_sub, frobSq_add, fip_add_left, fip_of_isHermitian hP.1,
      fip_of_isHermitian hP.1, fip_of_isHermitian hRpsd.1]
    ring
  have hPR : 0 ≤ rtrace (P * R) := rtrace_mul_nonneg hP hRpsd
  have hRN0 : rtrace (R * N) = 0 := by rw [hRN, rtrace_zero]
  have hNtr : 0 ≤ rtrace N := by
    rw [rtrace_eq_sum_diag]
    exact Finset.sum_nonneg fun i _ => psd_diag_re_nonneg hNpsd i
  have hQtr : rtrace Q = rtrace R - rtrace N := by
    rw [hQRN]
    unfold rtrace
    simp [Matrix.trace_sub]
  have hcN : 0 ≤ c * rtrace N := mul_nonneg hc.le hNtr
  rw [hexp, hQtr]
  linarith

/-- The rank-trace inequality specialised to `c = 2`. -/
theorem rank_trace_ineq_two {d r b : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) (hr : P.rank ≤ r) (hb : posIndex Q ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * b - frobSq (P + Q) ≤ r := by
  have h := rank_trace_ineq hP hQ hr hb (c := 2) (by norm_num)
  norm_num at h
  linarith

end Zeta23Redux.LinAlg

