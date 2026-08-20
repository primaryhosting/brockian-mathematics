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

lemma goodPrimesBelow_eventually_nonempty {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0) :
    ∀ᶠ N in atTop, (goodPrimesBelow W N).Nonempty := by
  obtain ⟨p₀, hp₀ge, hp₀prime⟩ := Nat.exists_infinite_primes (W.Δ.natAbs + 1)
  have hndvd : ¬ ((p₀ : ℤ) ∣ W.Δ) := by
    intro hdvd
    have h1 : (p₀ : ℤ) ≤ |W.Δ| := Int.le_of_dvd (abs_pos.mpr hΔ) ((dvd_abs _ _).mpr hdvd)
    rw [Int.abs_eq_natAbs] at h1
    have h2 : p₀ ≤ W.Δ.natAbs := by exact_mod_cast h1
    omega
  filter_upwards [Filter.eventually_ge_atTop p₀] with N hN
  refine ⟨p₀, ?_⟩
  simp only [goodPrimesBelow, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp₀prime, hndvd⟩

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `E` be an elliptic curve over `ℚ` given by an integral Weierstrass model `W` with
non-vanishing discriminant, and assume `E` has no complex multiplication.  Granting the
Weyl-criterion form `SatoTateWeyl W` of the Sato–Tate law (the input provided by the
automorphy of the symmetric power `L`-functions of a non-CM elliptic curve), the Frobenius
angles `θ_p ∈ [0, π]`, defined by `a_p = 2√p cos θ_p`, are equidistributed with respect to the
Sato–Tate measure: for `0 ≤ a ≤ b ≤ π` the proportion of primes of good reduction `p ≤ N`
with `θ_p ∈ [a, b]` converges to `(2/π) ∫_a^b sin² t dt`.

The non-CM hypothesis `hCM` is not used in this deduction: it is what guarantees the
hypothesis `hST` (for a CM curve the angles obey a different, non-Sato–Tate law). -/
