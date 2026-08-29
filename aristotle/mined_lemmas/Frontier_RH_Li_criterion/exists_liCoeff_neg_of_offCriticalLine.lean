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

theorem exists_liCoeff_neg_of_offCriticalLine :
    ∃ n : ℕ, 1 ≤ n ∧ liCoeff {(1 / 4 : ℂ), (3 / 4 : ℂ)} n < 0 := by
  have h0 : ∀ ρ ∈ ({(1 / 4 : ℂ), (3 / 4 : ℂ)} : Multiset ℂ), ρ ≠ 0 := by
    intro ρ hρ
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hρ
    rcases hρ with rfl | rfl <;> norm_num
  have hf : Multiset.map (fun ρ : ℂ => 1 - ρ) {(1 / 4 : ℂ), (3 / 4 : ℂ)}
      = {(1 / 4 : ℂ), (3 / 4 : ℂ)} := by
    show ((1 - (1 / 4 : ℂ)) ::ₘ (1 - (3 / 4 : ℂ)) ::ₘ 0 : Multiset ℂ) = _
    rw [show (1 - (1 / 4 : ℂ)) = 3 / 4 by ring, show (1 - (3 / 4 : ℂ)) = 1 / 4 by ring]
    exact Multiset.cons_swap _ _ _
  have hoff : ¬ ∀ ρ ∈ ({(1 / 4 : ℂ), (3 / 4 : ℂ)} : Multiset ℂ), ρ.re = 1 / 2 := by
    intro h
    have h1 := h (1 / 4) (by simp)
    norm_num at h1
  have h2 := mt (RH_Li_criterion _ h0 hf).mpr hoff
  push_neg at h2
  exact h2

/-! ### Application to the zeros of the completed Riemann zeta function

We apply the criterion to the (finitely many) zeros of the Riemann xi function inside a
symmetric box `0 ≤ Re s ≤ 1`, `|Im s| ≤ T`.  The Riemann xi function is realised in the
entire form `ξ(s) = s (1 - s) Λ(s) = s (1 - s) Λ₀(s) - 1`, where `Λ` is Mathlib's
`completedRiemannZeta` and `Λ₀` is `completedRiemannZeta₀`; away from `s = 0, 1` its zeros
are exactly the zeros of `Λ`, i.e. the nontrivial zeros of `ζ`. -/

/-- The Riemann xi function `ξ(s) = s (1 - s) Λ(s)`, written in a manifestly entire form. -/
