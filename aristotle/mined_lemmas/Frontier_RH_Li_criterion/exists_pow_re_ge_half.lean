import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Scope of this file.

Li's criterion states that the Riemann hypothesis holds iff the Li coefficients
`λ n = ∑_ρ (1 - (1 - 1/ρ)^n)` (the sum running over the nontrivial zeros of the Riemann zeta
function) are nonnegative for all `n ≥ 1`.  The arithmetic input -- the Hadamard factorisation of
the completed zeta function, which identifies `λ n` with a sum over the zeros -- is not available
in Mathlib.  What is formalised and proved here, unconditionally and without any extra axioms, is
the function-theoretic core of the criterion for a finite zero multiset: for a finite family of
nonzero complex numbers stable under the functional-equation symmetry `ρ ↦ 1 - ρ`, all members lie
on the critical line iff all Li coefficients of the family are nonnegative.  The hard direction is
the Bombieri--Lagarias style argument: if some `1 - 1/ρ` lies outside the closed unit disc, then a
compactness (simultaneous Dirichlet approximation) argument produces arbitrarily large exponents
`d` for which all `d`-th powers point into the right half plane, and the largest one then makes
`λ d` negative.
-/

open scoped BigOperators
open Finset Filter

namespace Frontier

/-- The `n`-th **Li coefficient** attached to a finite family of (nonzero) complex numbers
`ρ : ι → ℂ`, thought of as the zeros of a completed zeta function, listed with multiplicity:
`λ n = ∑ ρ, Re (1 - (1 - 1/ρ) ^ n)`. -/

lemma exists_pow_re_ge_half {ι : Type*} [Fintype ι] (z : ι → ℂ) (L : ℕ) :
    ∃ d, L ≤ d ∧ ∀ i, ‖z i‖ ^ d / 2 ≤ (z i ^ d).re := by
  classical
  set w : ι → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ) with hwdef
  have hw : ∀ i, ‖w i‖ = 1 := by
    intro i
    by_cases hz : z i = 0
    · simp [hwdef, hz]
    · simp [hwdef, hz, norm_ne_zero_iff.2 hz]
  have hbase : ∀ i, ((‖z i‖ : ℂ)) * w i = z i := by
    intro i
    by_cases hz : z i = 0
    · simp [hwdef, hz]
    · have h1 : (‖z i‖ : ℂ) ≠ 0 := by simpa using hz
      simp only [hwdef, hz, if_false]
      field_simp
  have hzw : ∀ (i : ι) (n : ℕ), z i ^ n = ((‖z i‖ : ℂ)) ^ n * w i ^ n := by
    intro i n; rw [← mul_pow, hbase]
  set F : ℕ → (ι → ℂ) := fun n i => w i ^ n with hFdef
  have hF : ∀ n, F n ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun i => ?_)
    rw [hFdef]
    simp [norm_pow, hw i]
  obtain ⟨a, -, φ, hφ, hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hF
  have hc : CauchySeq (F ∘ φ) := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨N, hN⟩ := hc (1 / 2) (by norm_num)
  have hmono : ∀ k : ℕ, φ N + k ≤ φ (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := hφ (show N + k < N + (k + 1) by omega)
        omega
  have hLd : φ N + L ≤ φ (N + L) := hmono L
  refine ⟨φ (N + L) - φ N, by omega, fun i => ?_⟩
  set d := φ (N + L) - φ N with hd
  have hsum : φ N + d = φ (N + L) := by omega
  have hdist : dist (F (φ (N + L)) i) (F (φ N) i) < 1 / 2 :=
    lt_of_le_of_lt (dist_le_pi_dist _ _ i) (hN (N + L) (by omega) N (by omega))
  have hkey : ‖w i ^ d - 1‖ < 1 / 2 := by
    have h1 : w i ^ (φ (N + L)) - w i ^ (φ N) = w i ^ (φ N) * (w i ^ d - 1) := by
      rw [mul_sub, mul_one, ← pow_add, hsum]
    have h2 : dist (F (φ (N + L)) i) (F (φ N) i) = ‖w i ^ (φ (N + L)) - w i ^ (φ N)‖ := by
      simp [hFdef, Complex.dist_eq]
    rw [h2, h1, norm_mul, norm_pow, hw i, one_pow, one_mul] at hdist
    exact hdist
  have hre : (1 : ℝ) / 2 ≤ (w i ^ d).re := by
    have h3 : (1 - w i ^ d).re ≤ ‖1 - w i ^ d‖ := Complex.re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h3
    rw [show ‖1 - w i ^ d‖ = ‖w i ^ d - 1‖ from norm_sub_rev _ _] at h3
    linarith
  calc ‖z i‖ ^ d / 2 = ‖z i‖ ^ d * (1 / 2) := by ring
    _ ≤ ‖z i‖ ^ d * (w i ^ d).re := mul_le_mul_of_nonneg_left hre (by positivity)
    _ = (z i ^ d).re := by rw [hzw i d, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- Hard direction: nonnegativity of all Li coefficients forces every `1 - 1/ρ` into the closed
unit disc. -/
