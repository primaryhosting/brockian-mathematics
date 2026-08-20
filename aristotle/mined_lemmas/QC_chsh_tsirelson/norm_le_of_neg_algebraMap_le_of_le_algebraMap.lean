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
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The quantum CHSH operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁`, built from a CHSH tuple of
observables in a C⋆-algebra (e.g. the bounded operators on a Hilbert space), has norm
at most `2√2`.  This is Tsirelson's bound.

The order-theoretic core is Mathlib's `tsirelson_inequality`
(`Mathlib/Algebra/Star/CHSH.lean`), which gives
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • 1`.
Here we upgrade that to a bound on the C⋆-norm: applying it also to the CHSH tuple
`(A₀, A₁, -B₀, -B₁)` yields the matching lower bound, and a two-sided order bound on a
selfadjoint element gives a norm bound.
-/

namespace QC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A selfadjoint element of a unital C⋆-algebra squeezed between `-r` and `r`
has norm at most `r`. -/

theorem norm_le_of_neg_algebraMap_le_of_le_algebraMap {a : A} {r : ℝ} (hr : 0 ≤ r)
    (ha : IsSelfAdjoint a) (h₁ : -(algebraMap ℝ A r) ≤ a) (h₂ : a ≤ algebraMap ℝ A r) :
    ‖a‖ ≤ r := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · simpa [Subsingleton.elim a 0] using hr
  · have hub : ∀ x ∈ spectrum ℝ a, x ≤ r :=
      (le_algebraMap_iff_spectrum_le (a := a) (r := r) ha).mp h₂
    have hlb : ∀ x ∈ spectrum ℝ a, -r ≤ x :=
      (algebraMap_le_iff_le_spectrum (a := a) (r := -r) ha).mp (by simpa using h₁)
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := a) ha with h | h
    · exact hub _ h
    · have := hlb _ h
      linarith

omit [PartialOrder A] [StarOrderedRing A] in
/-- The CHSH operator built from a CHSH tuple is selfadjoint. -/
