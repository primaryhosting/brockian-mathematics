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

import Brockian.EquidistributionBVReduction

/-!
# An equidistributed sequence

This file exhibits a concrete sequence in `[0,1)` satisfying
`Brockian.EquidistributionBVReduction.Equidistributed`, showing that the equidistribution
hypothesis of `configCount_density_of_BV` is satisfiable (so the theorem is not vacuous).

The sequence is the "triangular block" sequence: the `k`-th block lists the `k+1` points
`0/(k+1), 1/(k+1), …, k/(k+1)`.
-/

open Filter Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- Start index of block `k`; block `k` consists of the `k+1` indices
`blockStart k, …, blockStart k + k`. -/

lemma blockIdx_blockStart_add (k i : ℕ) (hi : i < k + 1) : blockIdx (blockStart k + i) = k := by
  have h2 : blockStart k + i < blockStart (k+1) := by rw [blockStart_succ]; omega
  set n := blockStart k + i with hn
  have hle : blockStart (blockIdx n) ≤ n := blockStart_blockIdx_le n
  have hlt : n < blockStart (blockIdx n + 1) := lt_blockStart_blockIdx_succ n
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt' | hgt
  · have : blockStart (blockIdx n + 1) ≤ blockStart k :=
      blockStart_strictMono.monotone (by omega)
    omega
  · have : blockStart (k+1) ≤ blockStart (blockIdx n) :=
      blockStart_strictMono.monotone (by omega)
    omega

/-- The triangular block sequence: the `k`-th block lists `0/(k+1), …, k/(k+1)`. -/
