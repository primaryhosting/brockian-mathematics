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

Li's criterion in its finite (unconditional, purely arithmetic-geometric) form.

Let `Z` be a finite multiset of nonzero complex numbers ("the zeros", listed with
multiplicity) which is stable under the functional-equation symmetry `ρ ↦ 1 - ρ`.
The associated Li coefficients are

`λ n = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`.

The main theorem `Frontier.RH_Li_criterion` states the equivalence

`(∀ ρ ∈ Z, Re ρ = 1/2)  ↔  (∀ n ≥ 1, 0 ≤ λ n)`,

i.e. "all zeros lie on the critical line" iff "all Li coefficients are nonnegative".

The forward direction uses that `Re ρ = 1/2` is equivalent to `|1 - 1/ρ| = 1`; the reverse
direction uses the functional-equation symmetry to produce a zero with `|1 - 1/ρ| > 1`, and
then a simultaneous-recurrence (pigeonhole/compactness) argument showing that the power sums
`∑ (1 - 1/ρ)^n` are unbounded above along a sequence of exponents.

The criterion is then applied to the actual zeros of the Riemann zeta function:

* `Frontier.RH_Li_criterion_completedZeta`: for each `T`, the zeros of the Riemann xi
  function inside the box `0 ≤ Re s ≤ 1`, `|Im s| ≤ T` (a finite set) all lie on the
  critical line iff their Li coefficients are all nonnegative;
* `Frontier.RH_iff_liCoeff_nonneg`: the Riemann hypothesis — every zero of the completed
  zeta function `Λ` has real part `1/2` — holds iff, for every truncation height `T`, all
  Li coefficients of the corresponding finite family of zeros are nonnegative.

The classical Li coefficients, which are sums over *all* nontrivial zeros, require a
convergence theory (Hadamard factorisation of `ξ`) that is not developed here; the
equivalences above use the truncated families instead.
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

namespace Frontier

open Complex Filter Finset

/-- The `n`-th Li coefficient attached to a multiset `Z` of "zeros":
`λ n = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`. -/

lemma zetaZeros_finite (T : ℝ) :
    {s : ℂ | riemannXi s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}.Finite := by
  by_contra hinf
  have hinf' : {s : ℂ | riemannXi s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}.Infinite := hinf
  have hK : IsCompact {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · refine IsClosed.inter (isClosed_le continuous_const Complex.continuous_re) ?_
      exact IsClosed.inter (isClosed_le Complex.continuous_re continuous_const)
        (isClosed_le Complex.continuous_im.abs continuous_const)
    · apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |T|))
      intro s hs
      obtain ⟨h1, h2, h3⟩ := hs
      simp only [Metric.mem_closedBall, dist_zero_right]
      have hb := Complex.norm_le_abs_re_add_abs_im s
      have hre : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
      have him : |s.im| ≤ |T| := le_trans h3 (le_abs_self T)
      linarith
  obtain ⟨x, -, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact hK fun s hs => hs.2
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hfreq : ∃ᶠ z in nhdsWithin x {x}ᶜ, riemannXi z = 0 := hacc.mono fun z hz => hz.1
  have hanal : AnalyticOnNhd ℂ riemannXi Set.univ :=
    differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ
  have heq := hanal.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ x) hfreq
  have hx0 := heq (Set.mem_univ 0)
  rw [riemannXi_zero] at hx0
  simp at hx0

/-- The zeros of `ξ` in the box `0 ≤ Re s ≤ 1`, `|Im s| ≤ T`, as a finite multiset. -/
