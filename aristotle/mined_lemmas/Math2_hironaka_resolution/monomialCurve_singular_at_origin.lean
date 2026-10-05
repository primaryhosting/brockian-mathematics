/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Math2

/-- The affine plane curve `C(m,n) = {(x,y) | y ^ n = x ^ m}`. -/

lemma monomialCurve_singular_at_origin {k : Type*} [Field k] {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ((0 : k), (0 : k)) ∈ monomialCurve k m n ∧
      MvPolynomial.eval (0 : Fin 2 → k) (monomialPoly k m n) = 0 ∧
      MvPolynomial.eval (0 : Fin 2 → k)
        (MvPolynomial.pderiv 0 (monomialPoly k m n)) = 0 ∧
      MvPolynomial.eval (0 : Fin 2 → k)
        (MvPolynomial.pderiv 1 (monomialPoly k m n)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [monomialCurve, zero_pow (by omega : m ≠ 0), zero_pow (by omega : n ≠ 0)]
  · simp [monomialPoly, zero_pow (by omega : m ≠ 0), zero_pow (by omega : n ≠ 0)]
  · simp [monomialPoly, zero_pow (by omega : m - 1 ≠ 0)]
  · simp [monomialPoly, zero_pow (by omega : n - 1 ≠ 0)]

/-- **Resolution of singularities for the monomial plane curves `y ^ n = x ^ m`.**

For coprime positive exponents `m`, `n` over a field `k` of characteristic zero (the
characteristic hypothesis is in fact not needed for the proof, but is kept because the statement
is asked for in characteristic `0`), the map `t ↦ (t ^ n, t ^ m)` is an injective parametrization
of the (for `m, n ≥ 2` singular) curve `{(x,y) | y ^ n = x ^ m}` by the smooth affine line, and
its image is exactly that curve.  This is an explicit instance of Hironaka's resolution of
singularities: the singular curve is the bijective image of a smooth variety. -/
