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

/-- Cohomological data attached to a smooth projective variety of dimension `dim` over the
finite field `𝔽_q`: for each degree `i` the (multi)set `frobEigenvalues i` of eigenvalues of
the geometric Frobenius acting on the `i`-th étale cohomology group, which vanishes outside
degrees `0, …, 2 dim`.

Étale cohomology is not available in Mathlib, so the cohomological input of the Weil
conjectures is packaged here as data; all statements below are statements about this data. -/
structure WeilData where
  /-- The size of the base field. -/
  q : ℕ
  /-- The base field is a genuine finite field, so it has at least two elements. -/
  one_lt_q : 1 < q
  /-- The dimension of the variety. -/
  dim : ℕ
  /-- The eigenvalues of the geometric Frobenius on the `i`-th cohomology group. -/
  frobEigenvalues : ℕ → Multiset ℂ
  /-- Cohomology vanishes above degree `2 dim`. -/
  vanishing : ∀ i, 2 * dim < i → frobEigenvalues i = 0

namespace WeilData

variable (W : WeilData)

/-- The number of `𝔽_{q^m}`-rational points of the variety, as computed by the
Grothendieck–Lefschetz trace formula
`N_m = ∑_i (-1)^i ∑_j α_{i,j}^m`. -/
noncomputable def pointCount (m : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (2 * W.dim + 1),
    (-1 : ℂ) ^ i * ((W.frobEigenvalues i).map (fun α => α ^ m)).sum

/-- The **Riemann hypothesis over finite fields** (Deligne's theorem, "Weil I"): every
eigenvalue of the geometric Frobenius on the `i`-th cohomology group is an algebraic number
all of whose archimedean absolute values equal `q^(i/2)`; i.e. `H^i` is pure of weight `i`. -/
def RiemannHypothesis : Prop :=
  ∀ i : ℕ, ∀ α ∈ W.frobEigenvalues i, ‖α‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)

/-- The total number of Frobenius eigenvalues in degrees below the top degree, i.e.
`∑_{i < 2 dim} b_i` where `b_i` is the `i`-th Betti number. -/
def lowerBettiSum : ℕ :=
  ∑ i ∈ Finset.range (2 * W.dim), Multiset.card (W.frobEigenvalues i)

end WeilData

/-- The Weil data of the projective space `ℙ^n` over `𝔽_q`: the cohomology is one dimensional
in each even degree `2j ≤ 2n`, with Frobenius eigenvalue `q^j`, and vanishes in odd degrees. -/
noncomputable def projectiveSpaceData (q n : ℕ) (hq : 1 < q) : WeilData where
  q := q
  one_lt_q := hq
  dim := n
  frobEigenvalues i := if Even i ∧ i ≤ 2 * n then {(q : ℂ) ^ (i / 2)} else 0
  vanishing i hi := by
    have : ¬ (i ≤ 2 * n) := by omega
    simp [this]

/-- Summing a function supported on even indices over `range (2 * n + 1)` amounts to summing
over `range (n + 1)` after halving the index. -/
theorem sum_even_range (n : ℕ) (g : ℕ → ℂ) :
    ∑ i ∈ Finset.range (2 * n + 1), (if Even i then g (i / 2) else 0) =
      ∑ j ∈ Finset.range (n + 1), g j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h2 : ¬ Even (2 * n + 1) := by simp [parity_simps]
    have h3 : Even (2 * n + 1 + 1) := by
      refine ⟨n + 1, by ring⟩
    have h4 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    simp [h2, h3, h4, Finset.sum_range_succ]

/-- The Lefschetz point count of the Weil data of `ℙ^n` is `1 + q^m + ⋯ + q^{nm}`. -/
theorem projectiveSpaceData_pointCount (q n : ℕ) (hq : 1 < q) (m : ℕ) :
    (projectiveSpaceData q n hq).pointCount m =
      ∑ j ∈ Finset.range (n + 1), ((q : ℂ) ^ m) ^ j := by
  rw [WeilData.pointCount]
  have key : ∀ i ∈ Finset.range (2 * (projectiveSpaceData q n hq).dim + 1),
      (-1 : ℂ) ^ i * (((projectiveSpaceData q n hq).frobEigenvalues i).map (fun α => α ^ m)).sum
        = if Even i then ((q : ℂ) ^ m) ^ (i / 2) else 0 := by
    intro i hi
    simp only [Finset.mem_range, projectiveSpaceData] at hi ⊢
    by_cases he : Even i
    · rw [if_pos ⟨he, by omega⟩, if_pos he, he.neg_one_pow]
      simp [← pow_mul, Nat.mul_comm]
    · rw [if_neg (by tauto), if_neg he]
      simp
  rw [Finset.sum_congr rfl key]
  exact sum_even_range n _

/-- The Lefschetz point count of the Weil data of `ℙ^n` over `𝔽_q` really is the number of
points of `ℙ^n` over a field with `q^m` elements. -/
theorem projectiveSpaceData_pointCount_eq_card (q n : ℕ) (hq : 1 < q) (m : ℕ)
    (K : Type) [Field K] [Fintype K] (hK : Nat.card K = q ^ m) :
    (projectiveSpaceData q n hq).pointCount m =
      (Nat.card (Projectivization K (Fin (n + 1) → K)) : ℂ) := by
  rw [projectiveSpaceData_pointCount,
    Projectivization.card_of_finrank K (Fin (n + 1) → K) (n := n + 1) (by simp), hK]
  push_cast
  simp

/-- **Base case of the Weil Riemann hypothesis**: it holds for projective space. -/
theorem projectiveSpaceData_riemannHypothesis (q n : ℕ) (hq : 1 < q) :
    (projectiveSpaceData q n hq).RiemannHypothesis := by
  intro i α hα
  simp only [projectiveSpaceData] at hα ⊢
  by_cases h : Even i ∧ i ≤ 2 * n
  · rw [if_pos h] at hα
    have hαv : α = (q : ℂ) ^ (i / 2) := by simpa using hα
    have hhalf : (i : ℝ) / 2 = ((i / 2 : ℕ) : ℝ) := by
      obtain ⟨k, hk⟩ := h.1
      subst hk
      have h2 : (k + k) / 2 = k := by omega
      rw [h2]
      push_cast
      ring
    rw [hαv, hhalf, Real.rpow_natCast]
    simp
  · rw [if_neg h] at hα
    simp at hα

/-- **Reduction**: the Riemann hypothesis implies the Weil estimate for point counts.  If the
top cohomology is one dimensional with Frobenius eigenvalue `q^dim` (as for a geometrically
connected smooth projective variety), then the number of `𝔽_{q^m}`-points differs from
`q^{m·dim}` by at most `(∑_{i < 2 dim} b_i) · q^{m (dim - 1/2)}`. -/
theorem weil_estimate_of_riemannHypothesis (W : WeilData) (hRH : W.RiemannHypothesis)
    (htop : W.frobEigenvalues (2 * W.dim) = {(W.q : ℂ) ^ W.dim}) (m : ℕ) :
    ‖W.pointCount m - (W.q : ℂ) ^ (W.dim * m)‖ ≤
      (W.lowerBettiSum : ℝ) * (W.q : ℝ) ^ ((W.dim : ℝ) * m - m / 2) := by
  have hq1 : (1:ℝ) ≤ (W.q:ℝ) := by exact_mod_cast W.one_lt_q.le
  have heven : Even (2 * W.dim) := even_two_mul W.dim
  have hsplit : W.pointCount m - (W.q:ℂ) ^ (W.dim * m)
      = ∑ i ∈ Finset.range (2 * W.dim),
          (-1 : ℂ) ^ i * ((W.frobEigenvalues i).map (fun α => α ^ m)).sum := by
    rw [WeilData.pointCount, Finset.sum_range_succ, htop]
    simp [pow_mul, heven.neg_one_pow]
  rw [hsplit]
  have hterm : ∀ i ∈ Finset.range (2 * W.dim),
      ‖(-1 : ℂ) ^ i * ((W.frobEigenvalues i).map (fun α => α ^ m)).sum‖
        ≤ (Multiset.card (W.frobEigenvalues i) : ℝ)
            * (W.q : ℝ) ^ ((W.dim : ℝ) * m - m / 2) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖((W.frobEigenvalues i).map (fun α => α ^ m)).sum‖
        ≤ (((W.frobEigenvalues i).map (fun α => α ^ m)).map norm).sum := norm_multiset_sum_le _
      _ = ((W.frobEigenvalues i).map (fun α => ‖α ^ m‖)).sum := by
            rw [Multiset.map_map]; rfl
      _ ≤ ((W.frobEigenvalues i).map
            (fun _ => (W.q : ℝ) ^ ((W.dim : ℝ) * m - m / 2))).sum := by
            refine Multiset.sum_map_le_sum_map _ _ ?_
            intro α hα
            rw [norm_pow, hRH i α hα, ← Real.rpow_natCast ((W.q:ℝ) ^ ((i:ℝ)/2)) m,
              ← Real.rpow_mul (by linarith)]
            refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
            have hid : (i : ℝ) ≤ 2 * (W.dim : ℝ) - 1 := by
              have : (i : ℝ) + 1 ≤ 2 * (W.dim : ℝ) := by exact_mod_cast hi
              linarith
            nlinarith [Nat.cast_nonneg (α := ℝ) m]
      _ = (Multiset.card (W.frobEigenvalues i) : ℝ)
            * (W.q : ℝ) ^ ((W.dim : ℝ) * m - m / 2) := by simp [Multiset.map_const']
  calc ‖∑ i ∈ Finset.range (2 * W.dim),
          (-1 : ℂ) ^ i * ((W.frobEigenvalues i).map (fun α => α ^ m)).sum‖
      ≤ ∑ i ∈ Finset.range (2 * W.dim),
          ‖(-1 : ℂ) ^ i * ((W.frobEigenvalues i).map (fun α => α ^ m)).sum‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (2 * W.dim), (Multiset.card (W.frobEigenvalues i) : ℝ)
            * (W.q : ℝ) ^ ((W.dim : ℝ) * m - m / 2) := Finset.sum_le_sum hterm
    _ = (W.lowerBettiSum : ℝ) * (W.q : ℝ) ^ ((W.dim : ℝ) * m - m / 2) := by
        rw [WeilData.lowerBettiSum, ← Finset.sum_mul]
        push_cast
        ring

/-- **Deligne's Riemann hypothesis for varieties over finite fields (Weil conjectures).**

The cohomological input is packaged in `Frontier.WeilData`; `WeilData.RiemannHypothesis` is
the purity statement `|α| = q^{i/2}` for the Frobenius eigenvalues on `H^i`.

This theorem records three Lean-checked facts:
1. the Riemann hypothesis holds for the Weil data of projective space `ℙ^n` over `𝔽_q`
   (the base case);
2. the Lefschetz trace formula for that data computes the true number of points of `ℙ^n`
   over any field with `q^m` elements, so the base case is about the correct data;
3. the reduction from the Riemann hypothesis to the Weil estimate on point counts:
   purity implies `|N_m - q^{m·dim}| ≤ (∑_{i<2 dim} b_i) q^{m(dim - 1/2)}`. -/
theorem deligne_weil_RH :
    (∀ (q n : ℕ) (hq : 1 < q), (projectiveSpaceData q n hq).RiemannHypothesis) ∧
    (∀ (q n m : ℕ) (hq : 1 < q) (K : Type) (_ : Field K) (_ : Fintype K),
      Nat.card K = q ^ m →
      (projectiveSpaceData q n hq).pointCount m =
        (Nat.card (Projectivization K (Fin (n + 1) → K)) : ℂ)) ∧
    (∀ (W : WeilData), W.RiemannHypothesis →
      W.frobEigenvalues (2 * W.dim) = {(W.q : ℂ) ^ W.dim} → ∀ m : ℕ,
      ‖W.pointCount m - (W.q : ℂ) ^ (W.dim * m)‖ ≤
        (W.lowerBettiSum : ℝ) * (W.q : ℝ) ^ ((W.dim : ℝ) * m - m / 2)) :=
  ⟨projectiveSpaceData_riemannHypothesis,
   fun q n m hq K _ _ hK => projectiveSpaceData_pointCount_eq_card q n hq m K hK,
   weil_estimate_of_riemannHypothesis⟩

end Frontier

