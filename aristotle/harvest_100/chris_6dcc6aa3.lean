/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Zeta23Redux.LinAlg

/-- Abel summation / Hardy–Littlewood–Pólya: if `m` is decreasing on `range d` and the partial
sums of `f` are dominated by those of `g`, with equal total sums, then `∑ m f ≤ ∑ m g`. -/
lemma abel_le (d : ℕ) (m f g : ℕ → ℝ)
    (hm : ∀ i j, i ≤ j → j < d → m j ≤ m i)
    (hpart : ∀ k, k ≤ d → ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, g i)
    (htot : ∑ i ∈ range d, f i = ∑ i ∈ range d, g i) :
    ∑ i ∈ range d, m i * f i ≤ ∑ i ∈ range d, m i * g i := by
  set h : ℕ → ℝ := fun i => f i - g i with hh
  have key : ∑ i ∈ range d, m i * h i ≤ 0 := by
    have hbp := Finset.sum_range_by_parts m h d
    simp only [smul_eq_mul] at hbp
    have h0 : ∑ i ∈ range d, h i = 0 := by
      simp [hh, Finset.sum_sub_distrib, htot]
    rw [hbp, h0, mul_zero, zero_sub, neg_nonpos]
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    have hle : m (i + 1) ≤ m i := hm i (i + 1) (by omega) (by omega)
    have hs : ∑ j ∈ range (i + 1), h j ≤ 0 := by
      have := hpart (i + 1) (by omega)
      simp only [hh, Finset.sum_sub_distrib]
      linarith
    nlinarith
  have hsplit : ∑ i ∈ range d, m i * h i
      = ∑ i ∈ range d, m i * f i - ∑ i ∈ range d, m i * g i := by
    simp [hh, mul_sub, Finset.sum_sub_distrib]
  linarith [key, hsplit]

/-- If `0 ≤ c j ≤ 1` with `∑_{j<d} c j = k` and `n` is decreasing, then
`∑_{j<d} c j * n j ≤ ∑_{j<k} n j`. -/
lemma partial_le (d k : ℕ) (hk : k ≤ d) (c n : ℕ → ℝ)
    (hc0 : ∀ j, j < d → 0 ≤ c j) (hc1 : ∀ j, j < d → c j ≤ 1)
    (hsum : ∑ j ∈ range d, c j = (k : ℝ))
    (hn : ∀ i j, i ≤ j → j < d → n j ≤ n i) :
    ∑ j ∈ range d, c j * n j ≤ ∑ j ∈ range k, n j := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simp only [Nat.cast_zero] at hsum
    have hz : ∀ j ∈ range d, c j * n j = 0 := by
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      have hcj : c j = 0 := by
        by_contra hne
        have hpos : 0 < c j := lt_of_le_of_ne (hc0 j hjd) (Ne.symm hne)
        have : 0 < ∑ j ∈ range d, c j :=
          Finset.sum_pos' (fun i hi => hc0 i (Finset.mem_range.mp hi)) ⟨j, hj, hpos⟩
        linarith
      simp [hcj]
    rw [Finset.sum_congr rfl hz]
    simp
  · set p := k - 1 with hp
    have hpd : p < d := by omega
    set chi : ℕ → ℝ := fun j => if j < k then 1 else 0 with hchi
    have hfil : (range d).filter (fun j => j < k) = range k := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
    have hsum2 : ∑ j ∈ range d, chi j * n j = ∑ j ∈ range k, n j := by
      simp only [hchi, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfil]
    have hsum3 : ∑ j ∈ range d, (c j - chi j) = 0 := by
      rw [Finset.sum_sub_distrib, hsum]
      have hck : ∑ j ∈ range d, chi j = (k : ℝ) := by
        simp only [hchi]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfil]
        simp
      rw [hck]; ring
    have key : ∑ j ∈ range d, (c j - chi j) * (n j - n p) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      by_cases hjk : j < k
      · have h1 : c j - chi j ≤ 0 := by simp only [hchi, if_pos hjk]; linarith [hc1 j hjd]
        have h2 : 0 ≤ n j - n p := by linarith [hn j p (by omega) hpd]
        nlinarith
      · have h1 : 0 ≤ c j - chi j := by simp only [hchi, if_neg hjk]; linarith [hc0 j hjd]
        have h2 : n j - n p ≤ 0 := by linarith [hn p j (by omega) hjd]
        nlinarith
    have expand : ∑ j ∈ range d, (c j - chi j) * (n j - n p)
        = (∑ j ∈ range d, c j * n j - ∑ j ∈ range d, chi j * n j)
          - n p * ∑ j ∈ range d, (c j - chi j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum3, hsum2, mul_zero, sub_zero] at expand
    linarith [key, expand.le, expand.symm.le]

/-- The doubly stochastic bilinear bound: for a doubly stochastic matrix `S` and decreasing
sequences `m`, `n` we have `∑_{i,j} m i * n j * S i j ≤ ∑_i m i * n i`. -/
lemma dstoch_le (d : ℕ) (S : ℕ → ℕ → ℝ) (m n : ℕ → ℝ)
    (hS0 : ∀ i j, i < d → j < d → 0 ≤ S i j)
    (hrow : ∀ i, i < d → ∑ j ∈ range d, S i j = 1)
    (hcol : ∀ j, j < d → ∑ i ∈ range d, S i j = 1)
    (hm : ∀ i j, i ≤ j → j < d → m j ≤ m i)
    (hn : ∀ i j, i ≤ j → j < d → n j ≤ n i) :
    ∑ i ∈ range d, ∑ j ∈ range d, m i * n j * S i j ≤ ∑ i ∈ range d, m i * n i := by
  set t : ℕ → ℝ := fun i => ∑ j ∈ range d, S i j * n j with ht
  have hrewrite : ∑ i ∈ range d, ∑ j ∈ range d, m i * n j * S i j
      = ∑ i ∈ range d, m i * t i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ht]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hrewrite]
  apply abel_le d m t n hm
  · intro k hkd
    have hcomm : ∑ i ∈ range k, t i = ∑ j ∈ range d, (∑ i ∈ range k, S i j) * n j := by
      rw [ht, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_mul])
    rw [hcomm]
    apply partial_le d k hkd _ n
    · intro j hj
      exact Finset.sum_nonneg
        (fun i hi => hS0 i j (by have := Finset.mem_range.mp hi; omega) hj)
    · intro j hj
      calc ∑ i ∈ range k, S i j ≤ ∑ i ∈ range d, S i j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hkd)
            intro i hi _
            exact hS0 i j (Finset.mem_range.mp hi) hj
        _ = 1 := hcol j hj
    · rw [Finset.sum_comm]
      have hone : ∀ i ∈ range k, ∑ j ∈ range d, S i j = 1 := fun i hi =>
        hrow i (by have := Finset.mem_range.mp hi; omega)
      rw [Finset.sum_congr rfl hone]
      simp
    · exact hn
  · rw [ht, Finset.sum_comm]
    have hone : ∀ j ∈ range d, ∑ i ∈ range d, S i j * n j = n j := by
      intro j hj
      rw [← Finset.sum_mul, hcol j (Finset.mem_range.mp hj), one_mul]
    rw [Finset.sum_congr rfl hone]

/-- The doubly stochastic bilinear bound, indexed by `Fin d`. -/
lemma dstoch_le_fin {d : ℕ} (mu nu : Fin d → ℝ) (T : Fin d → Fin d → ℝ)
    (hT0 : ∀ i j, 0 ≤ T i j)
    (hTrow : ∀ i, ∑ j, T i j = 1) (hTcol : ∀ j, ∑ i, T i j = 1)
    (hmuAnti : Antitone mu) (hnuAnti : Antitone nu) :
    ∑ i, ∑ j, mu i * nu j * T i j ≤ ∑ i, mu i * nu i := by
  set m : ℕ → ℝ := fun i => if h : i < d then mu ⟨i, h⟩ else 0 with hm'
  set n : ℕ → ℝ := fun j => if h : j < d then nu ⟨j, h⟩ else 0 with hn'
  set S : ℕ → ℕ → ℝ := fun i j =>
    if hi : i < d then (if hj : j < d then T ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0 with hS'
  have key := dstoch_le d S m n ?_ ?_ ?_ ?_ ?_
  · have hR : ∑ i ∈ range d, m i * n i = ∑ i, mu i * nu i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => m i * n i) d]
      exact Finset.sum_congr rfl fun i _ => by simp [hm', hn']
    have hL : ∑ i ∈ range d, ∑ j ∈ range d, m i * n j * S i j
        = ∑ i, ∑ j, mu i * nu j * T i j := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range d, m i * n j * S i j) d]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun j => m i * n j * S i j) d]
      exact Finset.sum_congr rfl fun j _ => by simp [hm', hn', hS']
    rw [hL, hR] at key
    exact key
  · intro i j hi hj; simp [hS', hi, hj, hT0]
  · intro i hi
    rw [← Fin.sum_univ_eq_sum_range (fun j => S i j) d]
    rw [show (∑ j : Fin d, S i j) = ∑ j : Fin d, T ⟨i, hi⟩ j from
      Finset.sum_congr rfl fun j _ => by simp [hS', hi]]
    exact hTrow ⟨i, hi⟩
  · intro j hj
    rw [← Fin.sum_univ_eq_sum_range (fun i => S i j) d]
    rw [show (∑ i : Fin d, S i j) = ∑ i : Fin d, T i ⟨j, hj⟩ from
      Finset.sum_congr rfl fun i _ => by simp [hS', hj]]
    exact hTcol ⟨j, hj⟩
  · intro i j hij hjd
    have hid : i < d := by omega
    simp only [hm', dif_pos hid, dif_pos hjd]
    exact hmuAnti hij
  · intro i j hij hjd
    have hid : i < d := by omega
    simp only [hn', dif_pos hid, dif_pos hjd]
    exact hnuAnti hij

/-- The trace of `diag x * W * diag y * Wᴴ` in terms of the entrywise squared moduli of `W`. -/
lemma trace_conj_diag {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d → ℝ) :
    Matrix.trace (Matrix.diagonal (fun i => (x i : ℂ)) * W *
        Matrix.diagonal (fun j => (y j : ℂ)) * star W)
      = ∑ i, ∑ j, ((x i * y j * Complex.normSq (W i j) : ℝ) : ℂ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul,
    Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, RCLike.star_def]
  ring

/-- Rows of the entrywise squared-modulus matrix of a unitary matrix sum to one. -/
lemma normSq_row_sum {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (h : W * star W = 1) (i : Fin d) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h2 := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h2
  have h3 : ∑ j, ((Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ => by rw [Complex.mul_conj]
  have h4 : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast; simpa using h3
  exact_mod_cast h4

/-- Columns of the entrywise squared-modulus matrix of a unitary matrix sum to one. -/
lemma normSq_col_sum {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (h : star W * W = 1) (j : Fin d) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h2 := congrFun (congrFun h j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h2
  have h3 : ∑ i, ((Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_conj_mul_self]
  have h4 : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast; simpa using h3
  exact_mod_cast h4

/-- Diagonalising both Hermitian matrices turns `trace (A * B)` into a conjugated diagonal
trace, with `W = Uᴴ V` the unitary intertwining the two eigenbases. -/
lemma trace_mul_eq_conj_diag {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.trace (A * B) = Matrix.trace (
      Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
        (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
          (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *
      Matrix.diagonal (fun j => ((hB.eigenvalues j : ℝ) : ℂ)) *
      star (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ))) := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hV
  set Dm : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) with hDm
  set Dn : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) with hDn
  have hAeq : A = U * Dm * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hDm, hU]
    simp [Function.comp_def]
  have hBeq : B = V * Dn * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hDn, hV]
    simp [Function.comp_def]
  rw [hAeq, hBeq, Matrix.star_mul, star_star]
  have h1 : U * Dm * star U * (V * Dn * star V) = U * (Dm * (star U * V) * Dn * star V) := by
    simp [mul_assoc]
  rw [h1, Matrix.trace_mul_comm, mul_assoc]

/-- **Von Neumann's trace inequality** for Hermitian matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in decreasing order, then
`Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (mu nu : Fin d → ℝ) (sA sB : Equiv.Perm (Fin d))
    (hmu : ∀ i, mu i = hA.eigenvalues (sA i))
    (hnu : ∀ i, nu i = hB.eigenvalues (sB i))
    (hmuAnti : Antitone mu) (hnuAnti : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  rw [trace_mul_eq_conj_diag hA hB, trace_conj_diag]
  simp only [Complex.re_sum, Complex.ofReal_re]
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hV
  set W : Matrix (Fin d) (Fin d) ℂ := star U * V with hW
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hVV : star V * V = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hVV' : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hB.eigenvectorUnitary.2
  have hWs : star W = star V * U := by rw [hW, Matrix.star_mul, star_star]
  have hW1 : W * star W = 1 := by
    rw [hW, hWs]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by simp [mul_assoc]
      _ = 1 := by rw [hVV', mul_one, hUU]
  have hW2 : star W * W = 1 := by
    rw [hW, hWs]
    calc star V * U * (star U * V) = star V * (U * star U) * V := by simp [mul_assoc]
      _ = 1 := by rw [hUU', mul_one, hVV]
  have reindex : ∑ k, ∑ l, hA.eigenvalues k * hB.eigenvalues l * Complex.normSq (W k l)
      = ∑ i, ∑ j, mu i * nu j * Complex.normSq (W (sA i) (sB j)) := by
    rw [← Equiv.sum_comp sA
      (fun k => ∑ l, hA.eigenvalues k * hB.eigenvalues l * Complex.normSq (W k l))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp sB
      (fun l => hA.eigenvalues (sA i) * hB.eigenvalues l * Complex.normSq (W (sA i) l))]
    exact Finset.sum_congr rfl fun j _ => by rw [hmu, hnu]
  rw [reindex]
  refine dstoch_le_fin mu nu (fun i j => Complex.normSq (W (sA i) (sB j)))
    (fun i j => Complex.normSq_nonneg _) ?_ ?_ hmuAnti hnuAnti
  · intro i
    rw [Equiv.sum_comp sB (fun l => Complex.normSq (W (sA i) l))]
    exact normSq_row_sum W hW1 _
  · intro j
    rw [Equiv.sum_comp sA (fun k => Complex.normSq (W k (sB j)))]
    exact normSq_col_sum W hW2 _

/-- Every finite tuple of reals can be reindexed by a permutation so as to become decreasing. -/
lemma exists_antitone_reindex {d : ℕ} (f : Fin d → ℝ) :
    ∃ s : Equiv.Perm (Fin d), Antitone (fun i => f (s i)) := by
  refine ⟨Tuple.sort (fun i => -f i), ?_⟩
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -f i) hij
  simp only [Function.comp_apply] at h
  linarith

/-- Existence form of von Neumann's trace inequality: the decreasing eigenvalue listings always
exist, so the hypotheses of `vonNeumann_trace_ineq` are never vacuous. -/
theorem exists_vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ mu nu : Fin d → ℝ, Antitone mu ∧ Antitone nu ∧
      (∃ sA : Equiv.Perm (Fin d), ∀ i, mu i = hA.eigenvalues (sA i)) ∧
      (∃ sB : Equiv.Perm (Fin d), ∀ i, nu i = hB.eigenvalues (sB i)) ∧
      (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨sA, hsA⟩ := exists_antitone_reindex hA.eigenvalues
  obtain ⟨sB, hsB⟩ := exists_antitone_reindex hB.eigenvalues
  exact ⟨fun i => hA.eigenvalues (sA i), fun i => hB.eigenvalues (sB i), hsA, hsB,
    ⟨sA, fun _ => rfl⟩, ⟨sB, fun _ => rfl⟩,
    vonNeumann_trace_ineq hA hB _ _ sA sB (fun _ => rfl) (fun _ => rfl) hsA hsB⟩

end Zeta23Redux.LinAlg

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

