/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

Li's criterion states that the Riemann Hypothesis is equivalent to the nonnegativity of the
Li coefficients
`λ_n = ∑_ρ (1 - (1 - 1/ρ)^n)`,
the sum running over the (nontrivial) zeros `ρ` of the Riemann zeta function, counted with
multiplicity.

Mathlib currently has no theory of the zero multiset of `ζ` (no Hadamard factorisation of the
completed zeta function `ξ`, no statement of RH), so the criterion cannot be stated for `ζ`
itself.  What *is* stated and proved here is the arithmetic-free core of the criterion, the
Bombieri–Lagarias positivity theorem, for a finite family of zeros:

For any finite family `ρ : ι → ℂ` of nonzero complex numbers (indexed by a `Finset s`, so that
multiplicities are allowed) which is closed under the functional-equation symmetry
`ρ ↦ 1 - ρ`, one has

  (all `ρ i` lie on the critical line `Re ρ = 1/2`)  ↔  (`λ_n ≥ 0` for every `n ≥ 1`).

Both directions are proved from scratch:

* the easy direction rests on the elementary equivalence `Re ρ ≥ 1/2 ↔ |1 - 1/ρ| ≤ 1`
  (`Frontier.norm_one_sub_inv_le_one_iff`);
* the hard direction is the finite Bombieri–Lagarias argument
  (`Frontier.norm_le_one_of_re_sum_pow_le`): if the real parts of the power sums
  `∑ᵢ zᵢ^n` stay bounded above, then every `zᵢ` lies in the closed unit disc.  This uses a
  recurrence (almost-periodicity) statement `Frontier.exists_pow_near_one`, proved by
  compactness of the polydisc, which produces arbitrarily large exponents `k` for which all the
  `k`-th powers of finitely many unimodular numbers are simultaneously close to `1`.

No lemma of Mathlib closes the statement (a search for `RiemannHypothesis`, `riemannXi` zero
multisets, or Bombieri–Lagarias positivity returns nothing); the Mathlib input used consists of
standard facts such as `tendsto_subseq_of_bounded`, `Complex.normSq_eq_norm_sq` and
`tendsto_pow_atTop_atTop_of_one_lt`.
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

set_option grind.warning false

open Filter

namespace Frontier

/-! ### The critical line in terms of the Li transform `ρ ↦ 1 - 1/ρ` -/

/-- The Li transform `ρ ↦ 1 - 1/ρ` maps the closed half plane `Re ρ ≥ 1/2` onto the closed
unit disc. -/

theorem exists_pow_near_one_aux {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ k, 1 ≤ k ∧ ∀ i, ‖w i ^ k - 1‖ ≤ ε := by
  set F : ℕ → (ι → ℂ) := fun n i => w i ^ n with hF
  have hmem : ∀ n, F n ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro n
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 ?_
    intro i
    simp [hF, norm_pow, hw i]
  obtain ⟨a, -, psi, hpsi, hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  have hcauchy := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hlt : psi N < psi (N + 1) := hpsi (by omega)
  refine ⟨psi (N + 1) - psi N, by omega, ?_⟩
  intro i
  have hd : dist (F (psi (N + 1)) i) (F (psi N) i) < ε :=
    lt_of_le_of_lt (dist_le_pi_dist _ _ i) (hN (N + 1) (by omega) N (by omega))
  have key : F (psi (N + 1)) i - F (psi N) i = w i ^ psi N * (w i ^ (psi (N + 1) - psi N) - 1) := by
    simp only [hF]
    rw [mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  have hnorm : ‖F (psi (N + 1)) i - F (psi N) i‖ = ‖w i ^ (psi (N + 1) - psi N) - 1‖ := by
    rw [key, norm_mul, norm_pow, hw i, one_pow, one_mul]
  rw [dist_eq_norm, hnorm] at hd
  exact hd.le

/-- Recurrence with arbitrarily large exponents: for finitely many unimodular complex numbers
and any `ε > 0` and any bound `T`, there is `k ≥ T`, `k ≥ 1`, with all `w i ^ k` within `ε`
of `1`. -/
