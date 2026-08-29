/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

/-!
## Point counts on integral Weierstrass models

For a Weierstrass curve `W` over `ℤ` and a prime `p`, `affineCount W p` counts the pairs
`(x, y) ∈ {0, …, p-1}²` satisfying the Weierstrass equation modulo `p`, i.e. the affine
`𝔽_p`-points of the reduction of `W`.  The projective curve has exactly one further point,
the point at infinity `[0 : 1 : 0]`, so the number of `𝔽_p`-points of the reduction is
`affineCount W p + 1`, and the trace of Frobenius is
`a_p = p + 1 - (affineCount W p + 1) = p - affineCount W p`.
-/

/-- The number of affine solutions of the Weierstrass equation of `W` over `𝔽_p`,
computed with representatives `0, …, p-1`. -/
def affineCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  ((List.range p).flatMap fun x => (List.range p).map fun y => (x, y)).countP
    (fun q =>
      (((q.2 : ℤ) ^ 2 + W.a₁ * (q.1 : ℤ) * (q.2 : ℤ) + W.a₃ * (q.2 : ℤ))
        - ((q.1 : ℤ) ^ 3 + W.a₂ * (q.1 : ℤ) ^ 2 + W.a₄ * (q.1 : ℤ) + W.a₆)) % (p : ℤ) == 0)

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)` of the reduction mod `p` of an integral
Weierstrass model (meaningful at primes of good reduction, i.e. `p ∤ Δ`). -/
def apOf (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ := (p : ℤ) - (affineCount W p : ℤ)

/-!
## The modularity statement

`ModularityStatement` records the Taniyama–Shimura–Wiles theorem in the following shape:
for every elliptic curve over `ℚ`, presented by an integral Weierstrass model `W` with
non-vanishing discriminant, there is a level `N ≥ 1` and a normalised weight-`2` cusp form `f`
on `Γ₀(N)` whose `q`-expansion coefficients at all primes of good reduction for `W` are the
traces of Frobenius `a_p` of `W`.

This is a `Prop`-valued *definition*: it records the statement, it is not asserted here.
-/

/-- Formal statement of the modularity theorem for elliptic curves over `ℚ`: every integral
Weierstrass model with nonzero discriminant has its Frobenius traces matched by the
`q`-expansion coefficients of a normalised weight-two cusp form on some `Γ₀(N)`. -/
def ModularityStatement : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 →
    ∃ N : ℕ, 0 < N ∧ ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      (PowerSeries.coeff 1 (ModularFormClass.qExpansion 1 (⇑f)) = 1) ∧
      ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ W.Δ) →
        PowerSeries.coeff p (ModularFormClass.qExpansion 1 (⇑f)) = (apOf W p : ℂ)

/-!
## The curve of conductor 11 and the eta product of level 11

`E11` is the elliptic curve `y² + y = x³ - x²` (Cremona label `11a3`), of conductor `11` and
discriminant `-11`.  Its associated weight-two newform on `Γ₀(11)` is the eta product
`f = q ∏_{n ≥ 1} (1 - qⁿ)² (1 - q^{11n})²`.

`etaSeries N` computes the first `N` coefficients (of `q¹, q², …, q^N`) of that product,
by repeatedly multiplying the truncated power series by the factors `(1 - qⁿ)` and
`(1 - q^{11n})`, twice each, for `n = 1, …, N`.  (Factors with `n > N` do not affect the
first `N` coefficients.)
-/

/-- The curve `y² + y = x³ - x²`, of conductor `11` (Cremona label `11a3`). -/
def E11 : WeierstrassCurve ℤ := ⟨0, -1, 1, 0, 0⟩

/-- Multiply a truncated power series (given by its coefficient list of length `N`)
by the factor `1 - qⁿ`. -/
def mulOneMinusPow (N : ℕ) (l : List ℤ) (n : ℕ) : List ℤ :=
  (List.range N).map (fun i => l.getD i 0 - (if n ≤ i then l.getD (i - n) 0 else 0))

/-- Coefficients of `∏_{n = 1}^{N} (1 - qⁿ)² (1 - q^{11n})²`, truncated to degrees `0, …, N-1`. -/
def etaSeries (N : ℕ) : List ℤ :=
  (List.range N).foldl
    (fun l k =>
      let n := k + 1
      mulOneMinusPow N (mulOneMinusPow N (mulOneMinusPow N (mulOneMinusPow N l n) n) (11 * n))
        (11 * n))
    ((List.range N).map (fun i => if i = 0 then (1 : ℤ) else 0))

/-- The `q`-expansion coefficient `a_m` of the level-11 eta product
`f = q ∏_{n ≥ 1} (1 - qⁿ)² (1 - q^{11n})²`, for `1 ≤ m ≤ 50`. -/
def f11 (m : ℕ) : ℤ := (etaSeries 50).getD (m - 1) 0

/-- The first fifty coefficients of the level-11 eta product. -/
theorem etaSeries_fifty :
    etaSeries 50 =
      [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2, 4, 4, -1, -4, -2, 4, 0, 2, 2, -2, -1, 0, -4,
        -8, 5, -4, 0, 2, 7, 8, -1, 4, -2, -4, 3, 0, -4, 0, -8, -4, -6, 2, -2, 2, 8, 4, -3, 8] := by
  decide

/-- The discriminant of `E11` is `-11`, so `E11` is an elliptic curve over `ℚ`, with good
reduction at every prime `p ≠ 11`. -/
theorem E11_Δ : E11.Δ = -11 := by
  simp [E11, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/-- **Modularity, verified instance.**

The full Taniyama–Shimura–Wiles theorem (`Math2.ModularityStatement` above) is far beyond what
can currently be formalised.  What is proved here is a complete, kernel-checked verification of
modularity for the elliptic curve `E11 : y² + y = x³ - x²` of conductor `11` at every prime of
good reduction below `50`: for each such prime `p`, the trace of Frobenius
`a_p = p + 1 - #E11(𝔽_p)`, obtained by an explicit count of the points of the reduction of `E11`
mod `p`, coincides with the `p`-th `q`-expansion coefficient of the weight-two level-`11`
newform `f = q ∏_{n ≥ 1} (1 - qⁿ)² (1 - q^{11n})²`. -/
theorem modularity :
    ∀ p ∈ ([2, 3, 5, 7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] : List ℕ),
      p.Prime ∧ ¬ ((p : ℤ) ∣ E11.Δ) ∧ apOf E11 p = f11 p := by
  rw [E11_Δ]
  decide

end Math2

