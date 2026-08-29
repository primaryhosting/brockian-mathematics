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

theorem RH_Li_criterion {ι : Type*} (s : Finset ι) (rho : ι → ℂ)
    (h0 : ∀ i ∈ s, rho i ≠ 0)
    (hsym : ∀ i ∈ s, ∃ j ∈ s, rho j = 1 - rho i) :
    (∀ i ∈ s, (rho i).re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff s rho n := by
  constructor
  · -- Easy direction: on the critical line, `|1 - 1/ρ| ≤ 1`, so every summand has
    -- nonnegative real part.
    intro hcrit n _
    rw [liCoeff, Complex.re_sum]
    refine Finset.sum_nonneg ?_
    intro i hi
    have hdisc : ‖1 - 1 / rho i‖ ≤ 1 :=
      (norm_one_sub_inv_le_one_iff (h0 i hi)).2 (le_of_eq (hcrit i hi).symm)
    have hpow : ‖(1 - 1 / rho i) ^ n‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hdisc
    have := Complex.re_le_norm ((1 - 1 / rho i) ^ n)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  · -- Hard direction: bounded power sums force all Li transforms into the closed unit disc,
    -- i.e. `Re ρ ≥ 1/2`; the symmetry `ρ ↦ 1 - ρ` then pins them to the critical line.
    intro hpos
    have hbound : ∀ n : ℕ, 1 ≤ n → (∑ i ∈ s, (1 - 1 / rho i) ^ n).re ≤ (s.card : ℝ) := by
      intro n hn
      have := hpos n hn
      rw [liCoeff_eq] at this
      linarith
    have hdisc := norm_le_one_of_re_sum_pow_le s (fun i => 1 - 1 / rho i) (s.card : ℝ) hbound
    have hhalf : ∀ i ∈ s, 1 / 2 ≤ (rho i).re := fun i hi =>
      (norm_one_sub_inv_le_one_iff (h0 i hi)).1 (hdisc i hi)
    intro i hi
    obtain ⟨j, hj, hji⟩ := hsym i hi
    have h1 := hhalf i hi
    have h2 := hhalf j hj
    rw [hji] at h2
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith

/-! ### Non-vacuity checks

The hypotheses of `RH_Li_criterion` are satisfiable by nonempty families, on and off the
critical line. -/

/-- A two-element family on the critical line, closed under `ρ ↦ 1 - ρ`: all its Li
coefficients are nonnegative. -/
example : ∀ n : ℕ, 1 ≤ n →
    0 ≤ liCoeff (Finset.univ : Finset (Fin 2)) ![(1 : ℂ) / 2 + Complex.I, 1 / 2 - Complex.I] n := by
  refine (RH_Li_criterion _ _ ?_ ?_).1 ?_
  · intro i _
    fin_cases i <;> simp [Complex.ext_iff]
  · intro i _
    fin_cases i
    · exact ⟨1, Finset.mem_univ _, by simp; ring⟩
    · exact ⟨0, Finset.mem_univ _, by simp; ring⟩
  · intro i _
    fin_cases i <;> simp

/-- A two-element family off the critical line, closed under `ρ ↦ 1 - ρ`: some Li coefficient
is negative. -/
example : ∃ n : ℕ, 1 ≤ n ∧
    liCoeff (Finset.univ : Finset (Fin 2)) ![(1 : ℂ) / 4, 3 / 4] n < 0 := by
  have h := (RH_Li_criterion (Finset.univ : Finset (Fin 2)) ![(1 : ℂ) / 4, 3 / 4] ?_ ?_).not
  · have hnot : ¬ ∀ i ∈ (Finset.univ : Finset (Fin 2)), (![(1 : ℂ) / 4, 3 / 4] i).re = 1 / 2 := by
      intro hc
      have := hc 0 (Finset.mem_univ _)
      norm_num at this
    have := h.1 hnot
    push_neg at this
    obtain ⟨n, hn, hlt⟩ := this
    exact ⟨n, hn, hlt⟩
  · intro i _
    fin_cases i <;> simp
  · intro i _
    fin_cases i
    · exact ⟨1, Finset.mem_univ _, by norm_num⟩
    · exact ⟨0, Finset.mem_univ _, by norm_num⟩

end Frontier

