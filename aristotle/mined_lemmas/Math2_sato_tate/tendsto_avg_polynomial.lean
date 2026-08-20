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

theorem tendsto_avg_polynomial
    (hS : ∀ᶠ N in atTop, (S N).Nonempty)
    (hU : ∀ n : ℕ, 1 ≤ n →
      Tendsto (fun N => avg (S N) θ
        (fun t => (Polynomial.Chebyshev.U ℝ n).eval (Real.cos t))) atTop (𝓝 0))
    (P : Polynomial ℝ) :
    Tendsto (fun N => avg (S N) θ (fun t => P.eval (Real.cos t))) atTop
      (𝓝 (∫ t, P.eval (Real.cos t) ∂satoTateMeasure)) := by
  refine chebyshevU_span_induction (motive := fun P : Polynomial ℝ =>
    Tendsto (fun N => avg (S N) θ (fun t => P.eval (Real.cos t))) atTop
      (𝓝 (∫ t, P.eval (Real.cos t) ∂satoTateMeasure))) ?_ ?_ ?_ P
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hfun : (fun t : ℝ => (Polynomial.Chebyshev.U ℝ ((0:ℕ) : ℤ)).eval (Real.cos t))
          = fun _ : ℝ => (1:ℝ) := by
        funext t; simp [Polynomial.Chebyshev.U_zero]
      rw [hfun]
      have hint : ∫ _t : ℝ, (1:ℝ) ∂satoTateMeasure = 1 := by simp
      rw [hint]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hS] with N hN using (avg_const (S N) θ 1 hN).symm
    · rw [integral_chebyshevU_satoTateMeasure n hn]
      exact hU n hn
  · intro c P hP
    have h1 : ∀ t : ℝ, (Polynomial.C c * P).eval (Real.cos t) = c * P.eval (Real.cos t) := by
      intro t; simp
    simp only [h1, avg_const_mul, MeasureTheory.integral_const_mul]
    exact hP.const_mul c
  · intro P Q hP hQ
    have h1 : ∀ t : ℝ, (P + Q).eval (Real.cos t)
        = P.eval (Real.cos t) + Q.eval (Real.cos t) := by
      intro t; simp
    simp only [h1, avg_add]
    rw [MeasureTheory.integral_add (integrable_of_continuous (continuous_eval_cos P))
      (integrable_of_continuous (continuous_eval_cos Q))]
    exact hP.add hQ

/-- Averages against continuous functions converge to the corresponding Sato–Tate integral. -/
