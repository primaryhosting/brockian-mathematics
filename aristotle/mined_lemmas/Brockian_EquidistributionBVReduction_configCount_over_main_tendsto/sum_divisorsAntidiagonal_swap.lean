import Mathlib

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

/-
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The named hypothesis `configCount_over_main_tendsto` of the equidistribution /
Bombieri–Vinogradov reduction is discharged here: it is Mertens' classical asymptotic
`∑_{q ≤ N} φ(q) ∼ 3 N² / π²`.

The proof follows the standard argument.  Möbius inversion of `∑_{d ∣ n} φ(d) = n`
(`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` applied to `Nat.sum_totient`) gives the
hyperbola expansion `∑_{q ≤ N} φ(q) = ∑_{d ≤ N} μ(d) · T(⌊N/d⌋)` with `T(m) = m(m+1)/2`.
Comparing `T(⌊N/d⌋)/N²` with `1/(2d²)` termwise costs `O(1/(Nd))`, so the error is
`O(H_N / N) → 0`, while the truncated Möbius sum converges to
`∑_{d ≥ 1} μ(d)/d² = 1/ζ(2) = 6/π²`; the last identity is taken from Mathlib
(`ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius`, `LSeries_zeta_eq_riemannZeta` and
`riemannZeta_two`).
-/

open ArithmeticFunction Finset Filter

namespace Brockian.EquidistributionBVReduction

/-- The number of *configurations* `(q, a)` with `1 ≤ q ≤ N`, `1 ≤ a ≤ q` and `gcd (a, q) = 1`;
these are the (modulus, primitive residue class) pairs available to an equidistribution /
Bombieri–Vinogradov style reduction with moduli up to `N`.  It equals `∑_{q ≤ N} φ(q)`. -/

theorem sum_divisorsAntidiagonal_swap (N : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ q ∈ Finset.Icc 1 N, ∑ p ∈ q.divisorsAntidiagonal, F p
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), F (d, e) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun x => (⟨x.2.1, x.2.2⟩ : (_ : ℕ) × ℕ))
    (j := fun y => (⟨y.1 * y.2, (y.1, y.2)⟩ : (_ : ℕ) × ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨hq1, hqN⟩, hde, hq0⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hde; omega)
    have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hde; omega)
    refine ⟨⟨hd0, ?_⟩, he0, ?_⟩
    · calc d ≤ d * e := Nat.le_mul_of_pos_right _ he0
        _ = q := hde
        _ ≤ N := hqN
    · rw [Nat.le_div_iff_mul_le hd0, mul_comm]; omega
  · rintro ⟨d, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hy ⊢
    obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hy
    rw [Nat.le_div_iff_mul_le hd1, mul_comm] at heN
    exact ⟨⟨by nlinarith, heN⟩, trivial, by positivity⟩
  · rintro ⟨q, d, e⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    simp [hx.2.1]
  · rintro ⟨d, e⟩ _
    rfl
  · rintro ⟨q, d, e⟩ _
    rfl

/-- Gauss' summation formula. -/
