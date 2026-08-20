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
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`.
(For a set with infinitely many points below `Λ` this is `0`, by the convention for
`Set.ncard`; the `Discrete` hypothesis below rules out that degenerate case.) -/

lemma eventuallyEq_counting_mul_ratio (S : Set ℝ) {C p : ℝ} (hC : 0 < C) :
    (fun L : ℝ => (C * L ^ p) * ((counting S L : ℝ) / (C * L ^ p)))
      =ᶠ[atTop] fun L : ℝ => (counting S L : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hpow : (0 : ℝ) < L ^ p := Real.rpow_pos_of_pos hL p
  have hne : (C * L ^ p) ≠ 0 := by positivity
  field_simp

/-- **The counting function diverges.**

If a spectrum `S ⊆ ℝ` is discrete and matches a Weyl law `N(Λ) ∼ C · Λ ^ p` with
`C > 0` and `p > 0`, then its eigenvalue counting function diverges:
`N(Λ) → ∞` as `Λ → ∞`.

The result is unconditional: nothing beyond discreteness and the Weyl-law match is
assumed. The discreteness hypothesis is retained because it is part of the intended
spectral setting, but the divergence already follows from the Weyl-law match alone. -/
