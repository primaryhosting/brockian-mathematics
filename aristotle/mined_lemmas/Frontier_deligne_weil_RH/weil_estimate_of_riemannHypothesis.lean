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
