import Brockian.Weyl.WeylLawTarget

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

import Mathlib
/-!
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* for a Weyl-law statement: a nondecreasing sequence of real
eigenvalue candidates `lam 0 ≤ lam 1 ≤ ⋯` which is unbounded above.  This is the
combinatorial data underlying the eigenvalue counting function of a Weyl law. -/
structure Candidate where
  /-- The candidate eigenvalues, listed with multiplicity in nondecreasing order. -/
  lam : ℕ → ℝ
  /-- The listing is nondecreasing. -/
  mono : Monotone lam
  /-- The listing is unbounded: only finitely many candidates lie below any threshold. -/
  unbounded : Filter.Tendsto lam Filter.atTop Filter.atTop

namespace Candidate

variable (C : Candidate)

/-- Below any threshold `t` only finitely many candidate eigenvalues occur. -/

theorem finite_below (t : ℝ) : {n : ℕ | C.lam n ≤ t}.Finite := by
  obtain ⟨N, hN⟩ := (C.unbounded.eventually_gt_atTop t).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hlt
  exact absurd hn (not_le.2 (hN n (not_lt.1 hlt)))

/-- The eigenvalue counting function `N(t) = #{n : lam n ≤ t}`. -/
