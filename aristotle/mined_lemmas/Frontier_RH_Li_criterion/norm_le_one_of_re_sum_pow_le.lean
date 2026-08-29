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

theorem norm_le_one_of_re_sum_pow_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) (C : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → (∑ i ∈ s, z i ^ n).re ≤ C) : ∀ i ∈ s, ‖z i‖ ≤ 1 := by
  intro i0 hi0
  by_contra hR
  push_neg at hR
  set R := ‖z i0‖ with hRdef
  have htend : Tendsto (fun k : ℕ => R ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hR
  obtain ⟨T, hT⟩ := (htend.eventually_gt_atTop (2 * C)).exists_forall_of_atTop
  set w : (↥s) → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ) with hwdef
  have hw : ∀ i : ↥s, ‖w i‖ = 1 := by
    intro i
    by_cases hz : z i = 0
    · simp [hwdef, hz]
    · simp [hwdef, hz]
  obtain ⟨k, hkT, hk1, hk⟩ := exists_pow_near_one w hw (ε := (1 : ℝ) / 2) (by norm_num) T
  have hterm : ∀ i ∈ s, ‖z i‖ ^ k / 2 ≤ (z i ^ k).re := by
    intro i hi
    by_cases hz : z i = 0
    · simp [hz, zero_pow (by omega : k ≠ 0)]
    · have hzn : (0 : ℝ) < ‖z i‖ := by simpa [norm_pos_iff] using hz
      have hsplit : z i = (‖z i‖ : ℂ) * w ⟨i, hi⟩ := by
        have hne : (‖z i‖ : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
        simp only [hwdef, hz, if_false]
        field_simp
      have hre : (1 : ℝ) / 2 ≤ (w ⟨i, hi⟩ ^ k).re := by
        have h1 := hk ⟨i, hi⟩
        have h2 : (1 - w ⟨i, hi⟩ ^ k).re ≤ ‖1 - w ⟨i, hi⟩ ^ k‖ := Complex.re_le_norm _
        rw [norm_sub_rev] at h2
        simp only [Complex.sub_re, Complex.one_re] at h2
        linarith
      have hexp : (z i ^ k).re = ‖z i‖ ^ k * (w ⟨i, hi⟩ ^ k).re := by
        conv_lhs => rw [hsplit]
        rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
      rw [hexp]
      have hp : (0 : ℝ) ≤ ‖z i‖ ^ k := by positivity
      nlinarith
  have hsum : (∑ i ∈ s, z i ^ k).re = ∑ i ∈ s, (z i ^ k).re := by simp [Complex.re_sum]
  have h1 : R ^ k / 2 ≤ ∑ i ∈ s, (z i ^ k).re := by
    calc R ^ k / 2 ≤ ∑ i ∈ s, ‖z i‖ ^ k / 2 :=
          Finset.single_le_sum (f := fun i => ‖z i‖ ^ k / 2) (fun i _ => by positivity) hi0
      _ ≤ _ := Finset.sum_le_sum hterm
  have h2 := h k hk1
  rw [hsum] at h2
  have h3 := hT k hkT
  linarith

/-! ### Li's coefficients and Li's criterion -/

/-- The `n`-th **Li coefficient** of a finite family of "zeros" `ρ : ι → ℂ` indexed by a
`Finset s`:  `λ_n = Re ∑_ρ (1 - (1 - 1/ρ)^n)`. -/
