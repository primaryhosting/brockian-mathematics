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

lemma abs_avg_sub_avg_le {S : Finset ℕ} {θ : ℕ → ℝ} {f g : ℝ → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ p ∈ S, |f (θ p) - g (θ p)| ≤ ε) : |avg S θ f - avg S θ g| ≤ ε := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp [avg, hε]
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  unfold avg
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  calc |∑ p ∈ S, (f (θ p) - g (θ p))| ≤ ∑ p ∈ S, |f (θ p) - g (θ p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, ε := Finset.sum_le_sum h
    _ = ε * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A continuous trapezoidal function: it equals `1` on `[a + e, b - e]`, vanishes outside
`[a, b]`, and interpolates linearly in between. -/
