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

def WeilDatum.RiemannHypothesis (W : WeilDatum) : Prop :=
  ∀ i, i ≤ 2 * W.dim → ∀ j : Fin (W.betti i), ‖W.root i j‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)

/-!
## An analytic input: power sums control the largest root

If the power sums `∑ j, α j ^ n` are `O(r ^ n)` then every `α j` has absolute value at
most `r`. This is the elementary (pigeonhole/compactness) form of the statement that the
generating function `∑ n, (∑ j, α j ^ n) z ^ n` has no pole in the disc `|z| < 1 / r`.
-/

/-- On a compact torus the powers `β ^ n` return arbitrarily close to `1`, simultaneously
for finitely many `β` of modulus one, with `n` arbitrarily large. -/
