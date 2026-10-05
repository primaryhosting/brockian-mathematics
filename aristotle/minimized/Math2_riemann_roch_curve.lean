/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
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

set_option grind.warning false

namespace Math2

/-- The degree of a divisor `D` on a curve whose (closed) points are indexed by `P`,
where `degPt p` is the degree of the point `p` (equal to `1` when the base field is
algebraically closed).  A divisor is a finitely supported formal `ℤ`-combination of points. -/

noncomputable def degDiv {P : Type*} (degPt : P → ℤ) (D : P →₀ ℤ) : ℤ :=
  D.sum fun p n => n * degPt p

@[simp]

theorem degDiv_add {P : Type*} (degPt : P → ℤ) (D E : P →₀ ℤ) :
    degDiv degPt (D + E) = degDiv degPt D + degDiv degPt E := by
  classical
  simp [degDiv, Finsupp.sum_add_index', add_mul]

@[simp]

theorem degDiv_single {P : Type*} (degPt : P → ℤ) (p : P) (n : ℤ) :
    degDiv degPt (Finsupp.single p n) = n * degPt p := by
  classical
  simp [degDiv, Finsupp.sum_single_index]

section RiemannRoch

variable {P : Type*} (degPt : P → ℤ) (g : ℕ) (K : P →₀ ℤ) (h0 h1 : (P →₀ ℤ) → ℕ)

/-- The Euler characteristic `χ(D) = h⁰(D) - h¹(D)` of the line bundle `O(D)`. -/

noncomputable def eulerChar (h0 h1 : (P →₀ ℤ) → ℕ) (D : P →₀ ℤ) : ℤ :=
  (h0 D : ℤ) - (h1 D : ℤ)

/-- Adding one point to a divisor increases the Euler characteristic by the degree of that
point; this is the additivity hypothesis, coming from the skyscraper exact sequence
`0 → O(D) → O(D + p) → k(p) → 0`.  Here it is restated for subtraction of a point. -/

theorem eulerChar_sub_single
    (hadd : ∀ (D : P →₀ ℤ) (p : P),
      eulerChar h0 h1 (D + Finsupp.single p 1) = eulerChar h0 h1 D + degPt p)
    (D : P →₀ ℤ) (p : P) :
    eulerChar h0 h1 (D - Finsupp.single p 1) = eulerChar h0 h1 D - degPt p := by
  have := hadd (D - Finsupp.single p 1) p
  rw [sub_add_cancel] at this
  omega

/-- The Euler characteristic along the line `D + n • p`, for `n : ℤ`. -/

theorem eulerChar_add_single
    (hadd : ∀ (D : P →₀ ℤ) (p : P),
      eulerChar h0 h1 (D + Finsupp.single p 1) = eulerChar h0 h1 D + degPt p)
    (D : P →₀ ℤ) (p : P) (n : ℤ) :
    eulerChar h0 h1 (D + Finsupp.single p n) = eulerChar h0 h1 D + n * degPt p := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hsplit : D + Finsupp.single p ((k : ℤ) + 1)
          = (D + Finsupp.single p (k : ℤ)) + Finsupp.single p 1 := by
        rw [add_assoc, ← Finsupp.single_add]
      rw [hsplit, hadd, ih]
      ring
  | pred k ih =>
      have hsplit : D + Finsupp.single p (-(k : ℤ) - 1)
          = (D + Finsupp.single p (-(k : ℤ))) - Finsupp.single p 1 := by
        rw [add_sub_assoc, ← Finsupp.single_sub]
      rw [hsplit, eulerChar_sub_single degPt h0 h1 hadd, ih]
      ring

/-- **Euler characteristic formula** (the "Riemann" half of Riemann–Roch):
under additivity of `χ` along points and the normalisations `h⁰(0) = 1`, `h¹(0) = g`,
one has `χ(D) = deg D + 1 - g` for every divisor `D`. -/

theorem eulerChar_eq
    (hzero : h0 0 = 1) (hgenus : h1 0 = g)
    (hadd : ∀ (D : P →₀ ℤ) (p : P),
      eulerChar h0 h1 (D + Finsupp.single p 1) = eulerChar h0 h1 D + degPt p)
    (D : P →₀ ℤ) :
    eulerChar h0 h1 D = degDiv degPt D + 1 - g := by
  classical
  induction D using Finsupp.induction with
  | zero => simp [eulerChar, hzero, hgenus]
  | single_add p n E _ _ ih =>
      have hcomm : Finsupp.single p n + E = E + Finsupp.single p n := by
        rw [add_comm]
      rw [hcomm, eulerChar_add_single degPt h0 h1 hadd, ih, degDiv_add, degDiv_single]
      ring

/-- **Riemann–Roch for a smooth projective curve.**

`P` indexes the closed points of the curve, a divisor is a finitely supported formal
`ℤ`-combination of points, `degPt p` is the degree of the point `p`, `K` is a canonical
divisor and `g` the genus.  The functions `h0 D = ℓ(D)` and `h1 D` record the dimensions
of `H⁰(O(D))` and `H¹(O(D))`.

The two geometric inputs are supplied as hypotheses:

* `hadd`: additivity of the Euler characteristic `χ = h⁰ - h¹` along a point, i.e. the long
  exact cohomology sequence of `0 → O(D) → O(D + p) → k(p) → 0`;
* `hduality`: Serre duality `h¹(D) = ℓ(K - D)`;

together with the normalisations `ℓ(0) = 1` and `h¹(0) = g` (the definition of the genus).

The conclusion is the Riemann–Roch formula `ℓ(D) - ℓ(K - D) = deg D + 1 - g`. -/

theorem riemann_roch_curve
    (hzero : h0 0 = 1) (hgenus : h1 0 = g)
    (hadd : ∀ (D : P →₀ ℤ) (p : P),
      eulerChar h0 h1 (D + Finsupp.single p 1) = eulerChar h0 h1 D + degPt p)
    (hduality : ∀ D : P →₀ ℤ, h1 D = h0 (K - D))
    (D : P →₀ ℤ) :
    (h0 D : ℤ) - (h0 (K - D) : ℤ) = degDiv degPt D + 1 - g := by
  have h := eulerChar_eq degPt g h0 h1 hzero hgenus hadd D
  rw [eulerChar, hduality D] at h
  exact h

/-- The degree of a canonical divisor is `2g - 2`: an immediate consequence of
Riemann–Roch applied to `D = K`. -/
