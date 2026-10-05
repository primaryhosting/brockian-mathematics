/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; it is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

set_option grind.warning false

namespace Frontier

/-!
## Li's criterion

Let `Z` be the multiset of (nontrivial) zeros of a completed zeta-type function.  Li's
coefficients are

`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`,

and Li's criterion states that all zeros lie on the critical line `Re ρ = 1/2` if and only if
`λ_n ≥ 0` for every `n ≥ 1`.

The content of the criterion is the Möbius change of variable `z = 1 - 1/ρ`, which maps the
critical line to the unit circle and the functional-equation symmetry `ρ ↦ 1 - ρ` to the
inversion `z ↦ 1/z`.  We prove the criterion for an arbitrary finite multiset of zeros which
avoids `0` and is stable under `ρ ↦ 1 - ρ`; this is the arithmetic-free core of Li's theorem
(the analytic input specific to `ζ`, namely the Hadamard product for the completed zeta
function, is what turns this statement into the statement about `ζ` itself).

The nontrivial direction uses a simultaneous recurrence statement on the unit circle
(`Frontier.exists_large_pow_near_one`): for finitely many unimodular numbers there are
arbitrarily large exponents `n` making all `n`-th powers simultaneously close to `1`.  This is
what forces a zero off the critical line to produce a negative Li coefficient.
-/

/-- The `n`-th Li coefficient attached to a finite multiset `Z` of zeros:
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`. -/

lemma exists_neg_of_one_lt_norm (W : Multiset ℂ) (hW : ∀ z ∈ W, z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ W) (hz₀' : 1 < ‖z₀‖) :
    ∃ n : ℕ, 1 ≤ n ∧ ((W.map (fun z => 1 - z ^ n)).sum).re < 0 := by
  obtain ⟨W', rfl⟩ := Multiset.exists_cons_of_mem hz₀
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (2 * (1 + (Multiset.card W' : ℝ))) hz₀'
  set N := max N₀ 1 with hNdef
  have hNle : ‖z₀‖ ^ N₀ ≤ ‖z₀‖ ^ N := pow_le_pow_right₀ hz₀'.le (le_max_left _ _)
  set u : (↥(z₀ ::ₘ W').toFinset) → ℂ := fun z => (z : ℂ) / (‖(z : ℂ)‖ : ℂ) with hu_def
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    have hi : (i : ℂ) ∈ z₀ ::ₘ W' := Multiset.mem_toFinset.mp i.2
    have hne : (i : ℂ) ≠ 0 := hW _ hi
    simp [hu_def, norm_ne_zero_iff.mpr hne]
  obtain ⟨n, hnN, hn⟩ := exists_large_pow_near_one u hu (ε := 1 / 2) (by norm_num) N
  have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hnN
  refine ⟨n, hn1, ?_⟩
  have hpt : ∀ z ∈ z₀ ::ₘ W', (1 / 2) * ‖z‖ ^ n ≤ (z ^ n).re := by
    intro z hz
    have hmem : z ∈ (z₀ ::ₘ W').toFinset := Multiset.mem_toFinset.mpr hz
    have hclose := hn ⟨z, hmem⟩
    have hre : (1 : ℝ) / 2 < ((z / (‖z‖ : ℂ)) ^ n).re := by
      have h1 : |(1 - (z / (‖z‖ : ℂ)) ^ n).re| ≤ ‖(1 - (z / (‖z‖ : ℂ)) ^ n)‖ :=
        Complex.abs_re_le_norm _
      have h2 : ‖(1 - (z / (‖z‖ : ℂ)) ^ n)‖ < 1 / 2 := by
        rw [show (1 - (z / (‖z‖ : ℂ)) ^ n) = -((z / (‖z‖ : ℂ)) ^ n - 1) by ring, norm_neg]
        exact hclose
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      simp only [Complex.sub_re, Complex.one_re] at h3
      linarith [h3.2]
    rw [re_pow_eq z n]
    have hnn : (0 : ℝ) ≤ ‖z‖ ^ n := by positivity
    nlinarith
  have hbig : 1 + (Multiset.card W' : ℝ) < (1 / 2) * ‖z₀‖ ^ n := by
    have h1 : ‖z₀‖ ^ N ≤ ‖z₀‖ ^ n := pow_le_pow_right₀ hz₀'.le hnN
    linarith
  rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
  have h1 : (1 - z₀ ^ n).re = 1 - (z₀ ^ n).re := by simp
  have h2 : ((W'.map (fun z => 1 - z ^ n)).sum).re ≤ (Multiset.card W' : ℝ) := by
    rw [re_multiset_sum, Multiset.map_map]
    have hb := Multiset.sum_le_card_nsmul (W'.map (Complex.re ∘ fun z => 1 - z ^ n)) (1 : ℝ) ?_
    · simpa using hb
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
      have hzz := hpt z (Multiset.mem_cons_of_mem hz)
      have hnn : (0 : ℝ) ≤ ‖z‖ ^ n := by positivity
      simp only [Function.comp_apply, Complex.sub_re, Complex.one_re]
      nlinarith
  have h3 := hpt z₀ (Multiset.mem_cons_self _ _)
  rw [h1]
  linarith

/-- **Li's criterion** for a finite multiset of zeros.

`Z` is a finite multiset of complex numbers ("the nontrivial zeros"), none of which is `0`,
which is stable under the functional-equation symmetry `ρ ↦ 1 - ρ`.  Then all elements of `Z`
lie on the critical line `Re ρ = 1/2` if and only if all the Li coefficients
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`, `n ≥ 1`, have nonnegative real part. -/
