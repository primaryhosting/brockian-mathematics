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

/-!
# Stone's theorem

A strongly continuous one-parameter unitary group `U : ℝ → (H →L[ℂ] H)` on a complex Hilbert
space `H` has a self-adjoint (in general unbounded) generator `A`, characterized by
`d/dt (U t x) |_{t=0} = i • A x`.
-/

namespace QPhys

open scoped InnerProductSpace
open Complex (I)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → (H →L[ℂ] H)) : Prop where
  /-- Each `U t` is a unitary operator. -/
  mem_unitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)
  /-- The group law. -/
  map_add : ∀ s t : ℝ, U (s + t) = U s * U t
  /-- Strong continuity. -/
  strong_continuous : ∀ x : H, Continuous fun t => U t x

namespace IsUnitaryGroup

variable {U : ℝ → (H →L[ℂ] H)} (hU : IsUnitaryGroup U)
include hU


def genGraph (U : ℝ → (H →L[ℂ] H)) : Submodule ℂ (H × H) where
  carrier := {p : H × H | HasDerivAt (fun t => U t p.1) (I • p.2) 0}
  add_mem' := by
    intro a b ha hb
    have := ha.add hb
    simpa [Set.mem_setOf_eq, map_add, smul_add] using this
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, map_zero, smul_zero]
    simpa using (hasDerivAt_const (0:ℝ) (0:H))
  smul_mem' := by
    intro c a ha
    have := ha.const_smul (c : ℂ)
    have hfun : (fun t => U t ((c • a).1)) = (c • fun t => U t a.1) := by
      funext t; simp [Prod.smul_fst]
    rw [Set.mem_setOf_eq, hfun]
    simpa [smul_comm c I] using this

omit [CompleteSpace H] in
