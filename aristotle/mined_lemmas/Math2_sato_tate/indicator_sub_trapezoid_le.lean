import Mathlib
import RequestProject.SatoTate.Equidistribution

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above is placed directly after the `import` lines, since Lean 4 requires
`import` commands to come first in a file.)

## Contents

We formalise the Sato–Tate distribution of Frobenius angles of an elliptic curve over `ℚ`,
given by an integral Weierstrass model `W`.

* `Math2.frobAngle W p` is the Frobenius angle `θ_p ∈ [0, π]` at a prime `p`, defined by
  `a_p = 2 √p cos θ_p` where `a_p = p + 1 - #E(𝔽_p)` is the trace of Frobenius.
* `Math2.satoTateDensity` is the Sato–Tate density `(2/π) sin²θ` and `Math2.satoTateMeasure`
  is the associated probability measure on `[0, π]`.
* `Math2.SatoTateWeyl W` is the Weyl-criterion form of the Sato–Tate law: the averages over
  primes of good reduction of `U n (cos θ_p)` tend to `0` for every `n ≥ 1`, where `U n` is
  the `n`-th Chebyshev polynomial of the second kind (the character of the `n`-th symmetric
  power of the standard representation of `SU(2)`).  This is exactly the statement supplied
  by the potential automorphy theorems for a non-CM elliptic curve over `ℚ`.
* `Math2.sato_tate` deduces from it the distributional form of the Sato–Tate law: the
  proportion of primes `p ≤ N` of good reduction whose Frobenius angle lies in `[a, b]`
  converges to `(2/π) ∫_a^b sin²t dt`.
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

namespace Math2

open Filter Topology MeasureTheory Set

/-- The number of points of the reduction of the integral Weierstrass model `W` modulo `p`
(including the point at infinity). -/

lemma indicator_sub_trapezoid_le {a b e : ℝ} (he : 0 < e) (t : ℝ) :
    Set.indicator (Icc a b) (1 : ℝ → ℝ) t - trapezoid a b e t
      ≤ Set.indicator (Icc a (a + e)) (1 : ℝ → ℝ) t
        + Set.indicator (Icc (b - e) b) (1 : ℝ → ℝ) t := by
  have hnn1 : (0:ℝ) ≤ Set.indicator (Icc a (a + e)) (1 : ℝ → ℝ) t :=
    Set.indicator_nonneg (by intro x _; norm_num) t
  have hnn2 : (0:ℝ) ≤ Set.indicator (Icc (b - e) b) (1 : ℝ → ℝ) t :=
    Set.indicator_nonneg (by intro x _; norm_num) t
  by_cases ht : t ∈ Icc a b
  · rw [Set.indicator_of_mem ht]
    by_cases hin : a + e ≤ t ∧ t ≤ b - e
    · rw [trapezoid_eq_one he hin.1 hin.2]
      simpa using add_nonneg hnn1 hnn2
    · have hle : (1:ℝ) - trapezoid a b e t ≤ 1 := by
        have := trapezoid_nonneg a b e t; linarith
      rcases not_and_or.1 hin with h | h
      · have hmem : t ∈ Icc a (a + e) := ⟨ht.1, le_of_lt (not_le.1 h)⟩
        rw [Set.indicator_of_mem hmem]
        simp only [Pi.one_apply]
        linarith
      · have hmem : t ∈ Icc (b - e) b := ⟨le_of_lt (not_le.1 h), ht.2⟩
        rw [Set.indicator_of_mem hmem]
        simp only [Pi.one_apply]
        linarith
  · rw [Set.indicator_of_notMem ht]
    have := trapezoid_nonneg a b e t
    linarith

