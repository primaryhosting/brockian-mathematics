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

theorem RH_Li_criterion_completedZeta (T : ℝ) :
    (∀ s : ℂ, riemannXi s = 0 → 0 ≤ s.re → s.re ≤ 1 → |s.im| ≤ T → s.re = 1 / 2)
      ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff (zetaZeroMultiset T) n := by
  have h0 : ∀ ρ ∈ zetaZeroMultiset T, ρ ≠ 0 := by
    intro ρ hρ hzero
    rw [mem_zetaZeroMultiset] at hρ
    rw [hzero, riemannXi_zero] at hρ
    simpa using hρ.1
  have hstab : ∀ s : ℂ, s ∈ (zetaZeros_finite T).toFinset ↔
      (1 - s) ∈ (zetaZeros_finite T).toFinset := by
    intro s
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, riemannXi_one_sub, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub, abs_neg]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, by linarith, by linarith, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, by linarith, by linarith, h4⟩
  have hfun : (zetaZeroMultiset T).map (fun ρ => 1 - ρ) = zetaZeroMultiset T := by
    have hinj : Set.InjOn (fun ρ : ℂ => 1 - ρ) ((zetaZeros_finite T).toFinset : Set ℂ) := by
      intro a _ b _ hab
      simpa using sub_right_injective hab
    rw [zetaZeroMultiset, ← Finset.image_val_of_injOn hinj]
    congr 1
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hstab y).mp hy
    · intro hx
      exact ⟨1 - x, (hstab x).mp hx, by ring⟩
  rw [← RH_Li_criterion (zetaZeroMultiset T) h0 hfun]
  constructor
  · intro h ρ hρ
    rw [mem_zetaZeroMultiset] at hρ
    exact h ρ hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2
  · intro h s h1 h2 h3 h4
    exact h s (mem_zetaZeroMultiset.mpr ⟨h1, h2, h3, h4⟩)

/-! ### The Riemann hypothesis itself -/

