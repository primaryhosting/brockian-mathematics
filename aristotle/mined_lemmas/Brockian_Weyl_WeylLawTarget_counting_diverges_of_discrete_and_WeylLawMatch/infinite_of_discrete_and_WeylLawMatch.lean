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

theorem infinite_of_discrete_and_WeylLawMatch
    (S : Set ℝ) (C p : ℝ) (hdisc : Discrete S) (hW : WeylLawMatch S C p) :
    S.Infinite := by
  intro hfin
  have hdiv := counting_diverges_of_discrete_and_WeylLawMatch S C p hdisc hW
  obtain ⟨L, hL⟩ := (hdiv.eventually_ge_atTop ((S.ncard : ℝ) + 1)).exists
  have hbound : counting S L ≤ S.ncard :=
    Set.ncard_le_ncard Set.inter_subset_left hfin
  have hbound' : ((counting S L : ℝ)) ≤ (S.ncard : ℝ) := by exact_mod_cast hbound
  linarith

/-!
## Non-vacuity

The hypotheses above are satisfiable: the spectrum `S = ℕ ⊆ ℝ` is discrete and matches
the Weyl law with `C = 1`, `p = 1`.
-/

/-- Counting function of the model spectrum `ℕ ⊆ ℝ`: for `Λ ≥ 0` it equals `⌊Λ⌋ + 1`. -/
