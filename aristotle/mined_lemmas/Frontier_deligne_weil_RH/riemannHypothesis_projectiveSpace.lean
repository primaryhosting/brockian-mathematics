/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Filter Metric

/-!
## The zeta datum of a variety over a finite field

Mathlib has no étale cohomology, so we formalize the *shape* of the Weil conjectures at
the level of the numerical data they concern: for a `d`-dimensional variety `X` over `𝔽_q`
one has Betti numbers `b i`, inverse roots `α i j` of the characteristic polynomials
`P i` of Frobenius on the `i`-th cohomology group, and point counts
`N n = #X(𝔽_{q^n})` linked by the Grothendieck–Lefschetz trace formula.

The Riemann hypothesis part of the Weil conjectures (Deligne, 1974) is the assertion that
every inverse root occurring in degree `i` has archimedean absolute value `q ^ (i / 2)`.
-/

/-- Numerical zeta-function data attached to a `dim`-dimensional variety over `𝔽_q`:
Betti numbers, the inverse roots of Frobenius in each cohomological degree, the point
counts over the extensions `𝔽_{q ^ n}`, and the Lefschetz trace formula relating them. -/
structure WeilDatum where
  /-- the cardinality of the base field -/
  q : ℕ
  /-- the base field is a genuine finite field -/
  hq : 1 < q
  /-- the dimension of the variety -/
  dim : ℕ
  /-- the Betti numbers -/
  betti : ℕ → ℕ
  /-- the inverse roots of Frobenius acting on the `i`-th cohomology group -/
  root : (i : ℕ) → Fin (betti i) → ℂ
  /-- `pointCount n` is the number of `𝔽_{q ^ n}`-points -/
  pointCount : ℕ → ℕ
  /-- cohomology vanishes above degree `2 * dim` -/
  betti_vanishing : ∀ i, 2 * dim < i → betti i = 0
  /-- the Grothendieck–Lefschetz trace formula -/
  lefschetz : ∀ n : ℕ, 1 ≤ n →
    (pointCount n : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1), (-1 : ℂ) ^ i * ∑ j, (root i j) ^ n

/-- The Riemann hypothesis for a zeta datum: every inverse root of Frobenius in
cohomological degree `i` has absolute value `q ^ (i / 2)` (Deligne's theorem, for the
data coming from a smooth projective variety). -/

theorem riemannHypothesis_projectiveSpace (q : ℕ) (hq : 1 < q) (d : ℕ) :
    (projectiveSpace q hq d).RiemannHypothesis := by
  intro i hi j
  by_cases he : Even i
  · obtain ⟨c, hc⟩ := he
    have hi2 : i / 2 = c := by omega
    have hq0 : (0 : ℝ) < q := by positivity
    show ‖(q : ℂ) ^ (i / 2)‖ = (q : ℝ) ^ ((i : ℝ) / 2)
    rw [hi2, norm_pow, Complex.norm_natCast]
    have : ((i : ℝ) / 2) = (c : ℝ) := by
      have : (i : ℝ) = 2 * c := by exact_mod_cast (by omega : i = 2 * c)
      rw [this]; ring
    rw [this, Real.rpow_natCast]
  · exfalso
    have hb : (projectiveSpace q hq d).betti i = 0 := by
      show (if (Even i ∧ i ≤ 2 * d) then 1 else 0) = 0
      simp [he]
    have hpos : 0 < (projectiveSpace q hq d).betti i :=
      lt_of_le_of_lt (Nat.zero_le _) j.isLt
    rw [hb] at hpos
    exact absurd hpos (lt_irrefl 0)

/-!
## Reduction: for curves, the Riemann hypothesis is the Hasse–Weil point count bound

For a smooth projective curve of genus `g` over `𝔽_q` the cohomology is `ℂ` in degree `0`
(Frobenius acting by `1`), of dimension `2 g` in degree `1` (inverse roots `α j`), and `ℂ`
in degree `2` (Frobenius acting by `q`); the functional equation pairs the `α j` so that
`α j * α (σ j) = q`.  We prove, in this situation, that the Riemann hypothesis is
*equivalent* to the point count estimate `|N n - q ^ n - 1| = O(q ^ (n / 2))`.
-/

/-- Betti numbers of a curve of genus `g`. -/
