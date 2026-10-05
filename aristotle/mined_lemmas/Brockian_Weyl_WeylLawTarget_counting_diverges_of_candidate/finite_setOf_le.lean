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
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* for a Weyl law: an enumeration `lam 0 ≤ lam 1 ≤ ⋯` of real
"eigenvalues", listed with multiplicity in nondecreasing order, which is unbounded above.
This is the data one starts from when asking whether the eigenvalue counting function obeys
a Weyl asymptotic. -/
structure SpectrumCandidate where
  /-- The eigenvalue enumeration. -/
  lam : ℕ → ℝ
  /-- Eigenvalues are listed in nondecreasing order. -/
  mono : Monotone lam
  /-- The enumeration is unbounded: the spectrum accumulates only at `+∞`. -/
  tendsto_atTop : Filter.Tendsto lam Filter.atTop Filter.atTop

variable (C : SpectrumCandidate)

/-- The set of indices whose eigenvalue does not exceed `t` is finite: since `lam n → ∞`,
only finitely many eigenvalues lie below any threshold. -/

theorem finite_setOf_le (t : ℝ) : {n : ℕ | C.lam n ≤ t}.Finite := by
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp C.tendsto_atTop (t + 1)).exists_forall_of_atTop
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hcon
  have hNn : N ≤ n := by simpa [Set.mem_Iio] using hcon
  have := hN n hNn
  linarith

/-- The eigenvalue counting function `N(t) = #{n : lam n ≤ t}` of a candidate spectrum. -/
