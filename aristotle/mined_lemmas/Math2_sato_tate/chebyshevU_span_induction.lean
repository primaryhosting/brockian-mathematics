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

lemma chebyshevU_span_induction {motive : Polynomial ℝ → Prop}
    (hU : ∀ n : ℕ, motive (Polynomial.Chebyshev.U ℝ n))
    (hsmul : ∀ (c : ℝ) (P : Polynomial ℝ), motive P → motive (Polynomial.C c * P))
    (hadd : ∀ P Q : Polynomial ℝ, motive P → motive Q → motive (P + Q))
    (P : Polynomial ℝ) : motive P := by
  suffices H : ∀ d : ℕ, ∀ P : Polynomial ℝ, P.natDegree ≤ d → motive P from H P.natDegree P le_rfl
  intro d
  induction d with
  | zero =>
    intro P hP
    have hPC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hP
    have h1 : Polynomial.C (P.coeff 0) = Polynomial.C (P.coeff 0) * Polynomial.Chebyshev.U ℝ 0 := by
      simp [Polynomial.Chebyshev.U_zero]
    rw [hPC, h1]
    exact hsmul _ _ (hU 0)
  | succ d ih =>
    intro P hP
    set c : ℝ := P.coeff (d + 1) with hc
    set Q : Polynomial ℝ :=
      P - Polynomial.C (c / 2 ^ (d + 1)) * Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ) with hQdef
    have hUdeg : (Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ)).natDegree = d + 1 :=
      Polynomial.Chebyshev.natDegree_U_natCast ℝ (d + 1)
    have hUcoeff : (Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ)).coeff (d + 1) = 2 ^ (d + 1) := by
      have := Polynomial.Chebyshev.leadingCoeff_U_natCast (R := ℝ) (d + 1)
      rwa [Polynomial.leadingCoeff, hUdeg] at this
    have hQ : Q.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hQdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with heq | hlt
      · rw [← heq, hUcoeff, ← hc]
        field_simp
        ring
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hUdeg]; exact hlt)]
        ring
    have hsplit : P = Q + Polynomial.C (c / 2 ^ (d + 1)) * Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ) := by
      rw [hQdef]; ring
    rw [hsplit]
    exact hadd _ _ (ih Q hQ) (hsmul _ _ (hU (d + 1)))

end Math2

