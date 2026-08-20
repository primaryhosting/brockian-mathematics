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

theorem isSelfAdjoint_chsh {A₀ A₁ B₀ B₁ : A} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsSelfAdjoint (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) := by
  have h : ∀ x y : A, star x = x → star y = y → x * y = y * x → star (x * y) = x * y := by
    intro x y hx hy hxy
    rw [star_mul, hx, hy, ← hxy]
  unfold IsSelfAdjoint
  rw [star_sub, star_add, star_add,
    h A₀ B₀ T.A₀_sa T.B₀_sa T.A₀B₀_commutes,
    h A₀ B₁ T.A₀_sa T.B₁_sa T.A₀B₁_commutes,
    h A₁ B₀ T.A₁_sa T.B₀_sa T.A₁B₀_commutes,
    h A₁ B₁ T.A₁_sa T.B₁_sa T.A₁B₁_commutes]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Negating both of Bob's observables in a CHSH tuple gives another CHSH tuple. -/
