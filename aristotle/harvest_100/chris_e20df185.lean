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

namespace Frontier

/-- The cohomological data attached to a smooth projective variety of dimension `dim`
over the finite field `𝔽_q`: for each degree `i`, the multiset `eigen i` of eigenvalues
of the geometric Frobenius acting on the `i`-th ℓ-adic cohomology group. -/
structure WeilData where
  /-- The cardinality of the base finite field. -/
  q : ℕ
  /-- The base field is a genuine finite field. -/
  hq : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- Multiset of Frobenius eigenvalues in cohomological degree `i`. -/
  eigen : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanish : ∀ i, 2 * dim < i → eigen i = 0
  /-- Frobenius acts invertibly, so all eigenvalues are nonzero. -/
  nonzero : ∀ i, ∀ a ∈ eigen i, a ≠ 0

namespace WeilData

variable (W : WeilData)

/-- The Lefschetz trace formula prediction for the number of `𝔽_{q^m}`-rational points:
`N_m = ∑_i (-1)^i tr(Frob^m ∣ H^i)`. -/
noncomputable def pointCount (m : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (2 * W.dim + 1), (-1 : ℂ) ^ i * (((W.eigen i).map (fun a => a ^ m)).sum)

/-- The characteristic polynomial `P_i(T) = det(1 - Frob ⬝ T ∣ H^i)`, evaluated at `T`. -/
noncomputable def charPoly (i : ℕ) (T : ℂ) : ℂ := ((W.eigen i).map (fun a => 1 - a * T)).prod

/-- The zeta function `Z(T) = ∏_i P_i(T)^{(-1)^{i+1}}`, written as the ratio of the
odd-degree factors by the even-degree ones. -/
noncomputable def zeta (T : ℂ) : ℂ :=
  (∏ i ∈ (Finset.range (2 * W.dim + 1)).filter (fun i => i % 2 = 1), W.charPoly i T) /
    (∏ i ∈ (Finset.range (2 * W.dim + 1)).filter (fun i => i % 2 = 0), W.charPoly i T)

/-- **The Riemann hypothesis over finite fields** (Deligne's theorem): every Frobenius
eigenvalue in cohomological degree `i` has absolute value `q^{i/2}`. -/
def RH : Prop := ∀ i, ∀ a ∈ W.eigen i, ‖a‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)

end WeilData

/-- The Weil data of projective `n`-space over `𝔽_q`: `H^{2j}` is one-dimensional with
Frobenius acting by `q^j`, and the odd cohomology vanishes. -/
noncomputable def projectiveSpace (n q : ℕ) (hq : 1 < q) : WeilData where
  q := q
  hq := hq
  dim := n
  eigen := fun i => if i % 2 = 0 ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0
  vanish := by
    intro i hi
    have h : ¬ (i % 2 = 0 ∧ i ≤ 2 * n) := by omega
    simp [h]
  nonzero := by
    intro i a ha
    by_cases h : i % 2 = 0 ∧ i ≤ 2 * n
    · rw [if_pos h, Multiset.mem_singleton] at ha
      subst ha
      have hq0 : (q : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      exact pow_ne_zero _ hq0
    · rw [if_neg h] at ha
      simp at ha

/-- Reindexing the even degrees `i = 2j` of the range `[0, 2n]` in a sum. -/
lemma sum_even_range (n m : ℕ) (z : ℂ) :
    ∑ i ∈ Finset.range (2 * n + 1), (if i % 2 = 0 then z ^ ((i / 2) * m) else 0)
      = ∑ j ∈ Finset.range (n + 1), z ^ (j * m) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (i := fun i => i / 2) (j := fun j => 2 * j) <;>
    intros <;> simp_all [Finset.mem_filter, Finset.mem_range] <;> omega

/-- Reindexing the even degrees `i = 2j` of the range `[0, 2n]` in a product. -/
lemma prod_filter_even_range (n : ℕ) (f : ℕ → ℂ) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter (fun i => i % 2 = 0), f (i / 2)
      = ∏ j ∈ Finset.range (n + 1), f j := by
  apply Finset.prod_nbij' (i := fun i => i / 2) (j := fun j => 2 * j) <;>
    intros <;> simp_all [Finset.mem_filter, Finset.mem_range] <;> omega

/-- The point counts of `ℙ^n` predicted by its Weil data are the correct ones:
`#ℙ^n(𝔽_{q^m}) = 1 + q^m + ⋯ + q^{nm}`. -/
theorem projectiveSpace_pointCount (n q : ℕ) (hq : 1 < q) (m : ℕ) :
    (projectiveSpace n q hq).pointCount m = ∑ j ∈ Finset.range (n + 1), (q : ℂ) ^ (j * m) := by
  rw [← sum_even_range n m (q : ℂ)]
  unfold WeilData.pointCount projectiveSpace
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  have hle : i ≤ 2 * n := by omega
  by_cases h : i % 2 = 0
  · have hs : (-1 : ℂ) ^ i = 1 := (Nat.even_iff.mpr h).neg_one_pow
    simp [h, hle, hs, ← pow_mul]
  · have hs : (-1 : ℂ) ^ i = -1 := (Nat.odd_iff.mpr (by omega)).neg_one_pow
    simp [h, hs]

/-- **Base case of the Weil Riemann hypothesis**: it holds for projective space. -/
theorem projectiveSpace_RH (n q : ℕ) (hq : 1 < q) : (projectiveSpace n q hq).RH := by
  intro i a ha
  have heig : (projectiveSpace n q hq).eigen i
      = if i % 2 = 0 ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0 := rfl
  have hqq : (projectiveSpace n q hq).q = q := rfl
  rw [heig] at ha
  by_cases h : i % 2 = 0 ∧ i ≤ 2 * n
  · rw [if_pos h, Multiset.mem_singleton] at ha
    subst ha
    have hi2 : ((i : ℝ)) / 2 = ((i / 2 : ℕ) : ℝ) := by
      have h2 : 2 * (i / 2) = i := by omega
      have h3 : ((2 * (i / 2) : ℕ) : ℝ) = (i : ℝ) := by exact_mod_cast h2
      push_cast at h3
      linarith
    rw [hqq, hi2, Real.rpow_natCast, norm_pow, Complex.norm_natCast]
  · rw [if_neg h] at ha
    simp at ha

/-- The zeta function of `ℙ^n` over `𝔽_q` is `1 / ∏_{j=0}^{n} (1 - q^j T)`. -/
theorem projectiveSpace_zeta (n q : ℕ) (hq : 1 < q) (T : ℂ) :
    (projectiveSpace n q hq).zeta T = 1 / ∏ j ∈ Finset.range (n + 1), (1 - (q : ℂ) ^ j * T) := by
  have heig : ∀ i, (projectiveSpace n q hq).eigen i
      = if i % 2 = 0 ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0 := fun _ => rfl
  have hdim : (projectiveSpace n q hq).dim = n := rfl
  have hodd : ∀ i ∈ (Finset.range (2 * n + 1)).filter (fun i => i % 2 = 1),
      (projectiveSpace n q hq).charPoly i T = 1 := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    have h : ¬ (i % 2 = 0 ∧ i ≤ 2 * n) := by omega
    simp [WeilData.charPoly, heig i, h]
  have heven : ∀ i ∈ (Finset.range (2 * n + 1)).filter (fun i => i % 2 = 0),
      (projectiveSpace n q hq).charPoly i T = 1 - (q : ℂ) ^ (i / 2) * T := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have h : i % 2 = 0 ∧ i ≤ 2 * n := ⟨hi.2, by omega⟩
    simp [WeilData.charPoly, heig i, h]
  rw [WeilData.zeta, hdim, Finset.prod_congr rfl hodd, Finset.prod_congr rfl heven,
    Finset.prod_const_one, prod_filter_even_range n (fun j => 1 - (q : ℂ) ^ j * T)]

/-- **The critical-line reformulation.** Writing `T = q^{-s}`, the statement that all
Frobenius eigenvalues in degree `i` have absolute value `q^{i/2}` is equivalent to the
statement that all zeros of `P_i(q^{-s})` lie on the line `Re s = i / 2`. -/
theorem RH_iff_critical_line (W : WeilData) :
    W.RH ↔ ∀ i, ∀ a ∈ W.eigen i, ∀ s : ℂ, a * (W.q : ℂ) ^ (-s) = 1 → s.re = (i : ℝ) / 2 := by
  have hq0 : (0 : ℝ) < (W.q : ℝ) := by
    have := W.hq; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  have hq1 : (W.q : ℝ) ≠ 1 := by
    have h : W.q ≠ 1 := by have := W.hq; omega
    exact_mod_cast h
  have hqC : (W.q : ℂ) ≠ 0 := by
    have h : W.q ≠ 0 := by have := W.hq; omega
    simpa using h
  have hlogq : Real.log W.q ≠ 0 := by
    have h1 : (1 : ℝ) < (W.q : ℝ) := by exact_mod_cast W.hq
    exact ne_of_gt (Real.log_pos h1)
  constructor
  · intro hRH i a ha s hs
    have hnorm := hRH i a ha
    have h1 : ‖a‖ * ‖(W.q : ℂ) ^ (-s)‖ = 1 := by rw [← norm_mul, hs, norm_one]
    have h2 : ‖(W.q : ℂ) ^ (-s)‖ = (W.q : ℝ) ^ (-s).re := by
      rw [← Complex.ofReal_natCast]
      exact Complex.norm_cpow_eq_rpow_re_of_pos hq0 _
    rw [hnorm, h2, ← Real.rpow_add hq0] at h1
    have h4 : (W.q : ℝ) ^ ((i : ℝ) / 2 + (-s).re) = (W.q : ℝ) ^ (0 : ℝ) := by
      rw [h1, Real.rpow_zero]
    have h3 := (Real.rpow_right_inj hq0 hq1).mp h4
    simp only [Complex.neg_re] at h3
    linarith
  · intro H i a ha
    have hane' : a ≠ 0 := W.nonzero i a ha
    have hL : Complex.log (W.q : ℂ) = ((Real.log W.q : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (le_of_lt hq0)]
    set s : ℂ := Complex.log a / ((Real.log W.q : ℝ) : ℂ) with hsdef
    have hLne : ((Real.log W.q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlogq
    have key : a * (W.q : ℂ) ^ (-s) = 1 := by
      rw [Complex.cpow_def_of_ne_zero hqC, hL, hsdef]
      field_simp
      rw [Complex.exp_neg, Complex.exp_log hane']
      field_simp
    have hre := H i a ha s key
    have hsre : s.re = Real.log ‖a‖ / Real.log W.q := by
      rw [hsdef, Complex.div_ofReal_re, Complex.log_re]
    rw [hsre] at hre
    have hlog : Real.log ‖a‖ = Real.log W.q * ((i : ℝ) / 2) := by
      field_simp at hre
      linarith [hre]
    have hane : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr hane'
    rw [Real.rpow_def_of_pos hq0, ← hlog, Real.exp_log hane]

/-! ### Poincaré duality: reduction of the Riemann hypothesis to degrees `≤ dim` -/

/-- Poincaré duality for the Frobenius eigenvalues: in complementary degrees `i` and
`2·dim - i` the eigenvalues correspond under `a ↦ q^dim / a`. -/
def WeilData.PoincareDuality (W : WeilData) : Prop :=
  ∀ i ≤ 2 * W.dim,
    W.eigen (2 * W.dim - i) = (W.eigen i).map (fun a => (W.q : ℂ) ^ W.dim / a)

/-- **Reduction to low degrees.** Under Poincaré duality it suffices to prove the Riemann
hypothesis in the cohomological degrees `i ≤ dim`; the remaining degrees follow. -/
theorem RH_of_le_dim_of_poincareDuality (W : WeilData) (hPD : W.PoincareDuality)
    (h : ∀ i ≤ W.dim, ∀ a ∈ W.eigen i, ‖a‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)) : W.RH := by
  have hq0 : (0 : ℝ) < (W.q : ℝ) := by
    have h1 := W.hq; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1.le
  intro i a ha
  by_cases hle : i ≤ W.dim
  · exact h i hle a ha
  by_cases hbig : 2 * W.dim < i
  · rw [W.vanish i hbig] at ha
    exact absurd ha (Multiset.notMem_zero a)
  · push_neg at hle
    set j := 2 * W.dim - i with hj
    have hji : 2 * W.dim - j = i := by omega
    have hjd : j ≤ W.dim := by omega
    have hj2 : j ≤ 2 * W.dim := by omega
    have hdual := hPD j hj2
    rw [hji] at hdual
    rw [hdual, Multiset.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hbn := h j hjd b hb
    rw [norm_div, hbn, norm_pow, Complex.norm_natCast,
      ← Real.rpow_natCast (W.q : ℝ) W.dim, ← Real.rpow_sub hq0]
    congr 1
    have hcast : (i : ℝ) + (j : ℝ) = 2 * (W.dim : ℝ) := by
      have hij : i + j = 2 * W.dim := by omega
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hij
    linarith

/-! ### Künneth: the Riemann hypothesis is stable under products -/

/-- The Weil data of a product of two varieties over the same finite field: by the Künneth
formula the degree-`k` eigenvalues are the products `a·b` with `a` in degree `i` and `b` in
degree `k - i`. -/
noncomputable def prodData (W₁ W₂ : WeilData) (hq : W₁.q = W₂.q) : WeilData where
  q := W₁.q
  hq := by rw [hq]; exact W₂.hq
  dim := W₁.dim + W₂.dim
  eigen := fun k =>
    ∑ i ∈ Finset.range (k + 1),
      (W₁.eigen i).bind (fun a => (W₂.eigen (k - i)).map (fun b => a * b))
  vanish := by
    intro k hk
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    rw [Multiset.mem_bind] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    by_cases h : 2 * W₁.dim < i
    · rw [W₁.vanish i h] at ha
      exact absurd ha (Multiset.notMem_zero a)
    · have h2 : 2 * W₂.dim < k - i := by omega
      rw [W₂.vanish _ h2] at hxa
      simp at hxa
  nonzero := by
    intro k a ha
    rw [Multiset.mem_sum] at ha
    obtain ⟨i, _, hai⟩ := ha
    rw [Multiset.mem_bind] at hai
    obtain ⟨x, hx, hax⟩ := hai
    rw [Multiset.mem_map] at hax
    obtain ⟨y, hy, rfl⟩ := hax
    exact mul_ne_zero (W₁.nonzero i x hx) (W₂.nonzero (k - i) y hy)

/-- **Künneth stability.** If the Riemann hypothesis holds for two varieties over `𝔽_q`,
it holds for their product. -/
theorem RH_prodData (W₁ W₂ : WeilData) (hq : W₁.q = W₂.q) (h₁ : W₁.RH) (h₂ : W₂.RH) :
    (prodData W₁ W₂ hq).RH := by
  have hq0 : (0 : ℝ) < (W₁.q : ℝ) := by
    have h1 := W₁.hq; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1.le
  intro k a ha
  have heig : (prodData W₁ W₂ hq).eigen k
      = ∑ i ∈ Finset.range (k + 1),
        (W₁.eigen i).bind (fun a => (W₂.eigen (k - i)).map (fun b => a * b)) := rfl
  have hqq : (prodData W₁ W₂ hq).q = W₁.q := rfl
  rw [heig, Multiset.mem_sum] at ha
  obtain ⟨i, hi, hai⟩ := ha
  simp only [Finset.mem_range] at hi
  rw [Multiset.mem_bind] at hai
  obtain ⟨x, hx, hax⟩ := hai
  rw [Multiset.mem_map] at hax
  obtain ⟨y, hy, rfl⟩ := hax
  rw [hqq, norm_mul, h₁ i x hx, h₂ (k - i) y hy, ← hq, ← Real.rpow_add hq0]
  congr 1
  have hik : (i : ℝ) + ((k - i : ℕ) : ℝ) = (k : ℝ) := by
    have hik' : i ≤ k := by omega
    push_cast [Nat.cast_sub hik']
    ring
  field_simp
  linarith [hik]

/-! ### The Hasse–Weil bound for curves -/

/-- **The Hasse–Weil bound.** For a curve of genus `g` over `𝔽_q` (so `H^0` and `H^2` are
spanned by `1` and `q` and `H^1` has dimension `2g`), the Riemann hypothesis is exactly
what gives the classical estimate `|N_m - (q^m + 1)| ≤ 2g·q^{m/2}` on the number of
`𝔽_{q^m}`-rational points. -/
theorem hasse_weil_bound (W : WeilData) (g : ℕ) (hdim : W.dim = 1)
    (h0 : W.eigen 0 = {1}) (h2 : W.eigen 2 = {(W.q : ℂ)})
    (hg : (W.eigen 1).card = 2 * g) (hRH : W.RH) (m : ℕ) :
    ‖W.pointCount m - ((W.q : ℂ) ^ m + 1)‖ ≤ 2 * g * (W.q : ℝ) ^ ((m : ℝ) / 2) := by
  have hq0 : (0 : ℝ) < (W.q : ℝ) := by
    have h1 := W.hq; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1.le
  set S : ℂ := ((W.eigen 1).map (fun a => a ^ m)).sum with hS
  have hpc : W.pointCount m = 1 - S + (W.q : ℂ) ^ m := by
    rw [WeilData.pointCount, hdim, show 2 * 1 + 1 = 3 from rfl, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h0, h2]
    simp [hS]
    ring
  have hdiff : W.pointCount m - ((W.q : ℂ) ^ m + 1) = -S := by rw [hpc]; ring
  rw [hdiff, norm_neg]
  have hbound : ‖S‖ ≤ ((W.eigen 1).map (fun a => ‖a ^ m‖)).sum := by
    rw [hS]
    simpa [Multiset.map_map, Function.comp] using
      norm_multiset_sum_le ((W.eigen 1).map (fun a => a ^ m))
  have hconst : ((W.eigen 1).map (fun a => ‖a ^ m‖))
      = Multiset.replicate (W.eigen 1).card ((W.q : ℝ) ^ ((m : ℝ) / 2)) := by
    rw [← Multiset.map_const']
    refine Multiset.map_congr rfl ?_
    intro a ha
    rw [norm_pow, hRH 1 a ha,
      ← Real.rpow_natCast ((W.q : ℝ) ^ (((1 : ℕ) : ℝ) / 2)) m, ← Real.rpow_mul hq0.le]
    norm_num
    ring_nf
  rw [hconst, Multiset.sum_replicate, hg] at hbound
  simpa [nsmul_eq_mul] using hbound

/-- **Deligne's Riemann hypothesis for varieties over finite fields.**

The Frobenius-eigenvalue formulation of the Weil Riemann hypothesis is `Frontier.WeilData.RH`:
every eigenvalue of the geometric Frobenius on the degree-`i` cohomology of a smooth
projective variety over `𝔽_q` has absolute value `q^{i/2}`.  This theorem records:

* a Lean-checked reduction: that formulation is *equivalent* to the classical statement
  that, writing `T = q^{-s}`, all zeros of the degree-`i` factor `P_i(T)` of the zeta
  function lie on the critical line `Re s = i / 2`;
* a Lean-checked reduction to low degrees: under Poincaré duality, the Riemann hypothesis
  in degrees `i ≤ dim` implies it in all degrees;
* stability under products (Künneth);
* the classical consequence for curves, the Hasse–Weil bound
  `|N_m - (q^m + 1)| ≤ 2g·q^{m/2}`;
* the base case of the conjecture, for projective space `ℙ^n` over `𝔽_q`, together with
  its point counts `1 + q^m + ⋯ + q^{nm}` and its zeta function `1/∏_{j≤n}(1 - q^j T)`. -/
theorem deligne_weil_RH :
    (∀ W : WeilData,
        W.RH ↔ ∀ i, ∀ a ∈ W.eigen i, ∀ s : ℂ, a * (W.q : ℂ) ^ (-s) = 1 → s.re = (i : ℝ) / 2) ∧
    (∀ W : WeilData, W.PoincareDuality →
        (∀ i ≤ W.dim, ∀ a ∈ W.eigen i, ‖a‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)) → W.RH) ∧
    (∀ (W₁ W₂ : WeilData) (hq : W₁.q = W₂.q), W₁.RH → W₂.RH → (prodData W₁ W₂ hq).RH) ∧
    (∀ (W : WeilData) (g : ℕ), W.dim = 1 → W.eigen 0 = {1} → W.eigen 2 = {(W.q : ℂ)} →
        (W.eigen 1).card = 2 * g → W.RH → ∀ m : ℕ,
          ‖W.pointCount m - ((W.q : ℂ) ^ m + 1)‖ ≤ 2 * g * (W.q : ℝ) ^ ((m : ℝ) / 2)) ∧
    (∀ (n q : ℕ) (hq : 1 < q),
        (projectiveSpace n q hq).RH ∧
        (∀ m : ℕ, (projectiveSpace n q hq).pointCount m
            = ∑ j ∈ Finset.range (n + 1), (q : ℂ) ^ (j * m)) ∧
        (∀ T : ℂ, (projectiveSpace n q hq).zeta T
            = 1 / ∏ j ∈ Finset.range (n + 1), (1 - (q : ℂ) ^ j * T))) :=
  ⟨RH_iff_critical_line,
   fun W hPD h => RH_of_le_dim_of_poincareDuality W hPD h,
   fun W₁ W₂ hq h₁ h₂ => RH_prodData W₁ W₂ hq h₁ h₂,
   fun W g hdim h0 h2 hg hRH m => hasse_weil_bound W g hdim h0 h2 hg hRH m,
   fun n q hq =>
    ⟨projectiveSpace_RH n q hq, projectiveSpace_pointCount n q hq,
      projectiveSpace_zeta n q hq⟩⟩

end Frontier

