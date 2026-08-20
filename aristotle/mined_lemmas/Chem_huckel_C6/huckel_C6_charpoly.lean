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

namespace Chem

open Polynomial

/-- The Hückel matrix of benzene (in units where the Coulomb integral `α` is `0` and the
resonance integral `β` is `1`): the adjacency matrix of the cycle graph `C₆`. -/

theorem huckel_C6_charpoly :
    C6adj.charpoly = ∏ k ∈ Finset.range 6, (X - C (2 * Real.cos (2 * Real.pi * k / 6))) := by
  rw [C6adj_charpoly, prod_cos_expand]

/-- **Hückel theory for benzene (`C₆`).**
A real number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₆` (i.e. there is a
nonzero vector `v` with `A *ᵥ v = μ • v`) if and only if `μ = 2·cos(2πk/6)` for some
`k ∈ {0, 1, 2, 3, 4, 5}`. -/
