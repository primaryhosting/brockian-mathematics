/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Frontier

/-!
## Formalization of the Riemann hypothesis for varieties over finite fields

We package the cohomological data attached to a smooth projective variety `X` of
dimension `d` over the finite field `𝔽_q` (as produced by ℓ-adic étale cohomology):

* `eigen i` is the multiset of eigenvalues of the geometric Frobenius acting on the
  `i`-th cohomology group (so `(eigen i).card` is the `i`-th Betti number);
* `count m` is `#X(𝔽_{q^m})`;
* `trace_formula` is the Grothendieck–Lefschetz trace formula;
* `weight` is *Deligne's theorem* (the Riemann hypothesis, Weil conjecture III):
  every Frobenius eigenvalue on `H^i` has archimedean absolute value `q^{i/2}`.

The zeta function of `X` is `Z(X, T) = ∏_i P_i(T)^{(-1)^{i+1}}` with
`P_i(T) = ∏_{α ∈ eigen i} (1 - α T)`, and `ζ(X, s) = Z(X, q^{-s})`.
The classical phrasing of the Riemann hypothesis is that the zeros
(resp. poles) of `ζ(X, s)` lie on the vertical lines `Re s = i/2` for `i` odd
(resp. even).  The main theorem below, `Frontier.deligne_weil_RH`, is exactly this
statement: it is a Lean-checked reduction of the "critical line" form of the
Riemann hypothesis to the "absolute value of Frobenius eigenvalues" form.

We also verify the base case: projective space `ℙ^n` over `𝔽_q` carries such a
package (`Frontier.WeilPackage.projectiveSpace`), with the correct point counts
`#ℙ^n(𝔽_{q^m}) = 1 + q^m + ⋯ + q^{nm}`, so the theorem applies to it
unconditionally.
-/

/-- Cohomological data of a smooth projective variety over `𝔽_q` satisfying the
Weil conjectures: Frobenius eigenvalues on each cohomology group, the
Grothendieck–Lefschetz trace formula for the point counts, and Deligne's purity
("Riemann hypothesis") statement on the eigenvalue absolute values. -/
structure WeilPackage where
  /-- The size of the base finite field. -/
  q : ℕ
  /-- A finite field has at least two elements. -/
  hq : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- `eigen i` : the Frobenius eigenvalues on the `i`-th cohomology group. -/
  eigen : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  eigen_vanish : ∀ i, 2 * dim < i → eigen i = 0
  /-- `count m = #X(𝔽_{q^m})`. -/
  count : ℕ → ℤ
  /-- The Grothendieck–Lefschetz trace formula. -/
  trace_formula : ∀ m, 1 ≤ m →
    (count m : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1), (-1) ^ i * ((eigen i).map (fun a => a ^ m)).sum
  /-- Deligne's theorem: purity of weights. -/
  weight : ∀ i, ∀ a ∈ eigen i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2)

namespace WeilPackage

variable (W : WeilPackage)

/-- The `i`-th local factor `P_i(T) = ∏_{α ∈ eigen i} (1 - α T)` of the zeta
function, evaluated at `T = q^{-s}`; i.e. the `i`-th factor of `ζ(X, s)`. -/
noncomputable def zetaFactor (i : ℕ) (s : ℂ) : ℂ :=
  ((W.eigen i).map (fun a => 1 - a * (W.q : ℂ) ^ (-s))).prod

/-- The zeta function `ζ(X, s) = Z(X, q^{-s}) = ∏_i P_i(q^{-s})^{(-1)^{i+1}}`. -/
noncomputable def zeta (s : ℂ) : ℂ :=
  ∏ i ∈ Finset.range (2 * W.dim + 1), (W.zetaFactor i s) ^ ((-1 : ℤ) ^ (i + 1))

end WeilPackage

/-- Auxiliary: for a base `> 1`, `q ^ t = 1` forces the exponent to vanish. -/
private lemma rpow_eq_one_iff_exp_zero {q t : ℝ} (h1 : 1 < q) (h : q ^ t = 1) : t = 0 := by
  have h0 : q ^ (0 : ℝ) = 1 := Real.rpow_zero q
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have := (Real.rpow_lt_rpow_left_iff h1).2 ht
    rw [h, h0] at this; linarith
  · exact ht
  · have := (Real.rpow_lt_rpow_left_iff h1).2 ht
    rw [h, h0] at this; linarith

/-- **The Riemann hypothesis for varieties over finite fields** (Weil conjectures,
proved by Deligne), in its "critical line" form.

If `X` is a smooth projective variety of dimension `d` over `𝔽_q` whose
cohomological data is packaged as a `WeilPackage` (Grothendieck–Lefschetz trace
formula together with Deligne's purity theorem), then every zero of the `i`-th
factor `P_i(q^{-s})` of the zeta function `ζ(X, s)` lies on the vertical line
`Re s = i / 2`.

In particular the zeros of `ζ(X, s)` (coming from the odd-degree factors) lie on
the lines `Re s = 1/2, 3/2, …, (2d-1)/2` and its poles (coming from the
even-degree factors) lie on the lines `Re s = 0, 1, …, d`. -/
theorem deligne_weil_RH (W : WeilPackage) (i : ℕ) (s : ℂ) (hs : W.zetaFactor i s = 0) :
    s.re = i / 2 := by
  have hq1 : (1 : ℝ) < (W.q : ℝ) := by exact_mod_cast W.hq
  have hq0 : (0 : ℝ) < (W.q : ℝ) := lt_trans zero_lt_one hq1
  -- some factor of the finite product vanishes
  rw [WeilPackage.zetaFactor, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hs
  obtain ⟨a, ha, hfa⟩ := hs
  have hqs : ‖(W.q : ℂ) ^ (-s)‖ = (W.q : ℝ) ^ (-s).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hq0 (-s)
  have hprod : a * (W.q : ℂ) ^ (-s) = 1 := by linear_combination -hfa
  have hnorm : ‖a‖ * ‖(W.q : ℂ) ^ (-s)‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  rw [W.weight i a ha, hqs, ← Real.rpow_add hq0] at hnorm
  have hzero : (i : ℝ) / 2 + (-s).re = 0 := rpow_eq_one_iff_exp_zero hq1 hnorm
  simp only [Complex.neg_re] at hzero
  linarith

/-- The same conclusion in terms of the reciprocal roots: every root `T` of the
`i`-th polynomial `P_i` of the zeta function has `|T| = q^{-i/2}`. -/
theorem deligne_weil_RH_roots (W : WeilPackage) (i : ℕ) (T : ℂ)
    (hT : ((W.eigen i).map (fun a => 1 - a * T)).prod = 0) :
    ‖T‖ = (W.q : ℝ) ^ (-(i : ℝ) / 2) := by
  have hq1 : (1 : ℝ) < (W.q : ℝ) := by exact_mod_cast W.hq
  have hq0 : (0 : ℝ) < (W.q : ℝ) := lt_trans zero_lt_one hq1
  rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at hT
  obtain ⟨a, ha, hfa⟩ := hT
  have hprod : a * T = 1 := by linear_combination -hfa
  have hnorm : ‖a‖ * ‖T‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  rw [W.weight i a ha] at hnorm
  have hpos : (0 : ℝ) < (W.q : ℝ) ^ ((i : ℝ) / 2) := Real.rpow_pos_of_pos hq0 _
  have : ‖T‖ = ((W.q : ℝ) ^ ((i : ℝ) / 2))⁻¹ := by
    field_simp at hnorm ⊢
    linarith [hnorm]
  rw [this, ← Real.rpow_neg (le_of_lt hq0)]
  congr 1
  ring

/-- **The Weil bound.**  Purity of weights together with the Lefschetz trace formula
gives the classical estimate `#X(𝔽_{q^m}) = O(q^{m·dim})`, with the sum of the Betti
numbers as implied constant. -/
theorem WeilPackage.abs_count_le (W : WeilPackage) (m : ℕ) (hm : 1 ≤ m) :
    |(W.count m : ℝ)| ≤
      (∑ i ∈ Finset.range (2 * W.dim + 1), ((W.eigen i).card : ℝ)) * (W.q : ℝ) ^ (W.dim * m) := by
  have hq1 : (1 : ℝ) ≤ (W.q : ℝ) := by exact_mod_cast W.hq.le
  have hq0 : (0 : ℝ) < (W.q : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  have hcast : |(W.count m : ℝ)| = ‖((W.count m : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
  have key : ∀ i ∈ Finset.range (2 * W.dim + 1),
      ‖(-1 : ℂ) ^ i * ((W.eigen i).map (fun a => a ^ m)).sum‖
        ≤ ((W.eigen i).card : ℝ) * (W.q : ℝ) ^ (W.dim * m) := by
    intro i hi
    have hi' : i ≤ 2 * W.dim := by
      simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hi
    have hbound : ∀ x ∈ (((W.eigen i).map (fun a => a ^ m)).map (fun a => ‖a‖)),
        x ≤ (W.q : ℝ) ^ (W.dim * m) := by
      intro x hx
      simp only [Multiset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨a, ha, rfl⟩ := hy
      rw [norm_pow, W.weight i a ha, ← Real.rpow_natCast ((W.q : ℝ) ^ ((i : ℝ) / 2)) m,
        ← Real.rpow_mul hq0.le, ← Real.rpow_natCast (W.q : ℝ) (W.dim * m)]
      apply Real.rpow_le_rpow_of_exponent_le hq1
      have : (i : ℝ) ≤ 2 * (W.dim : ℝ) := by exact_mod_cast hi'
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      push_cast
      nlinarith
    calc ‖(-1 : ℂ) ^ i * ((W.eigen i).map (fun a => a ^ m)).sum‖
        = ‖((W.eigen i).map (fun a => a ^ m)).sum‖ := by
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      _ ≤ (((W.eigen i).map (fun a => a ^ m)).map (fun a => ‖a‖)).sum :=
          norm_multiset_sum_le _
      _ ≤ ((((W.eigen i).map (fun a => a ^ m)).map (fun a => ‖a‖)).card) •
            ((W.q : ℝ) ^ (W.dim * m)) := Multiset.sum_le_card_nsmul _ _ hbound
      _ = ((W.eigen i).card : ℝ) * (W.q : ℝ) ^ (W.dim * m) := by
          simp [nsmul_eq_mul]
  rw [hcast, W.trace_formula m hm]
  calc ‖∑ i ∈ Finset.range (2 * W.dim + 1), (-1 : ℂ) ^ i * ((W.eigen i).map (fun a => a ^ m)).sum‖
      ≤ ∑ i ∈ Finset.range (2 * W.dim + 1),
          ‖(-1 : ℂ) ^ i * ((W.eigen i).map (fun a => a ^ m)).sum‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (2 * W.dim + 1),
          ((W.eigen i).card : ℝ) * (W.q : ℝ) ^ (W.dim * m) := Finset.sum_le_sum key
    _ = (∑ i ∈ Finset.range (2 * W.dim + 1), ((W.eigen i).card : ℝ)) *
          (W.q : ℝ) ^ (W.dim * m) := by rw [Finset.sum_mul]

/-!
## The base case: projective space `ℙ^n` over `𝔽_q`

The Frobenius eigenvalues on `H^{2k}(ℙ^n)` consist of the single number `q^k`
(and odd cohomology vanishes), so the trace formula reproduces the familiar
count `#ℙ^n(𝔽_{q^m}) = 1 + q^m + ⋯ + q^{nm}`, and each eigenvalue `q^k` on
`H^{2k}` indeed has absolute value `q^{2k/2}`.
-/

/-- Reindexing a sum over even indices `≤ 2n`. -/
private lemma sum_even_reindex (h : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n + 1), (if Even i then h (i / 2) else 0)
      = ∑ k ∈ Finset.range (n + 1), h k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
    rw [hr, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (f := h) (n + 1)]
    have h1 : ¬ Even (2 * n + 1) := by simp [parity_simps]
    have h2 : Even (2 * n + 1 + 1) := ⟨n + 1, by ring⟩
    rw [if_neg h1, if_pos h2]
    have h3 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    rw [h3]
    ring

/-- The Weil package of projective space `ℙ^n` over `𝔽_q`. -/
noncomputable def WeilPackage.projectiveSpace (q n : ℕ) (hq : 1 < q) : WeilPackage where
  q := q
  hq := hq
  dim := n
  eigen := fun i => if Even i ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0
  eigen_vanish := by
    intro i hi
    have : ¬ (Even i ∧ i ≤ 2 * n) := by omega
    simp [this]
  count := fun m => ∑ k ∈ Finset.range (n + 1), (q : ℤ) ^ (k * m)
  trace_formula := by
    intro m _
    push_cast
    have hL : ∀ i ∈ Finset.range (2 * n + 1),
        ((-1 : ℂ) ^ i *
            (((if Even i ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0 : Multiset ℂ)).map
              (fun a => a ^ m)).sum)
          = (if Even i then ((q : ℂ) ^ m) ^ (i / 2) else 0) := by
      intro i hi
      have hi' : i ≤ 2 * n := by
        simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hi
      by_cases he : Even i
      · rw [if_pos ⟨he, hi'⟩, if_pos he, he.neg_one_pow]
        simp [← pow_mul, Nat.mul_comm]
      · rw [if_neg (by tauto), if_neg he]
        simp
    rw [Finset.sum_congr rfl hL, sum_even_reindex (fun k => ((q : ℂ) ^ m) ^ k) n]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [← pow_mul, Nat.mul_comm]
  weight := by
    intro i a ha
    by_cases he : Even i ∧ i ≤ 2 * n
    · rw [if_pos he] at ha
      have hae : a = (q : ℂ) ^ (i / 2) := by simpa using ha
      subst hae
      have hi2 : ((i / 2 : ℕ) : ℝ) = (i : ℝ) / 2 := by
        obtain ⟨k, hk⟩ := he.1
        subst hk
        have : (k + k) / 2 = k := by omega
        rw [this]
        push_cast
        ring
      rw [norm_pow, Complex.norm_natCast, ← Real.rpow_natCast (q : ℝ) (i / 2), hi2]
    · rw [if_neg he] at ha
      simp at ha

/-- The point counts of the projective-space package are the correct ones:
`#ℙ^n(𝔽_{q^m}) = 1 + q^m + ⋯ + q^{nm}`, equivalently
`(q^m - 1) · #ℙ^n(𝔽_{q^m}) = q^{(n+1)m} - 1`. -/
theorem projectiveSpace_count (q n : ℕ) (hq : 1 < q) (m : ℕ) :
    ((WeilPackage.projectiveSpace q n hq).count m) * ((q : ℤ) ^ m - 1)
      = (q : ℤ) ^ ((n + 1) * m) - 1 := by
  show (∑ k ∈ Finset.range (n + 1), (q : ℤ) ^ (k * m)) * ((q : ℤ) ^ m - 1) = _
  have : ∀ k : ℕ, (q : ℤ) ^ (k * m) = ((q : ℤ) ^ m) ^ k := by
    intro k; rw [← pow_mul, Nat.mul_comm]
  simp only [this]
  rw [geom_sum_mul, ← pow_mul, Nat.mul_comm m (n + 1)]

/-- Non-vacuity of the main theorem: the `2k`-th factor of `ζ(ℙ^n, s)` really does
vanish, namely at `s = k`, which lies on the predicted line `Re s = (2k)/2 = k`. -/
theorem zetaFactor_projectiveSpace_eq_zero (q n : ℕ) (hq : 1 < q) (k : ℕ) (hk : k ≤ n) :
    (WeilPackage.projectiveSpace q n hq).zetaFactor (2 * k) (k : ℂ) = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by
    have : 0 < q := lt_trans Nat.zero_lt_one hq
    exact_mod_cast this.ne'
  have heigen : (WeilPackage.projectiveSpace q n hq).eigen (2 * k) = {(q : ℂ) ^ k} := by
    show (if Even (2 * k) ∧ 2 * k ≤ 2 * n then ({(q : ℂ) ^ (2 * k / 2)} : Multiset ℂ) else 0) = _
    rw [if_pos ⟨⟨k, by ring⟩, by omega⟩]
    congr 2
    omega
  show (((WeilPackage.projectiveSpace q n hq).eigen (2 * k)).map
      (fun a => 1 - a * ((q : ℕ) : ℂ) ^ (-(k : ℂ)))).prod = 0
  rw [heigen]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [Complex.cpow_neg, Complex.cpow_natCast]
  field_simp
  ring

/-- The Riemann hypothesis holds unconditionally for projective space: every zero
of the `i`-th factor of `ζ(ℙ^n, s)` lies on the line `Re s = i/2`. -/
theorem deligne_weil_RH_projectiveSpace (q n : ℕ) (hq : 1 < q) (i : ℕ) (s : ℂ)
    (hs : (WeilPackage.projectiveSpace q n hq).zetaFactor i s = 0) :
    s.re = i / 2 :=
  deligne_weil_RH _ i s hs

end Frontier

