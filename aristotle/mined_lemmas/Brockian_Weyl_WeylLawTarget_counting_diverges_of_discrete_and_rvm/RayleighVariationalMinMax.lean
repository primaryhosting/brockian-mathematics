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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S T` is the number of spectral points that are `≤ T`. -/

def RayleighVariationalMinMax (S : Set ℝ) : Prop := S.Infinite

/-- **Divergence of the counting function.**  If the spectrum `S` is discrete (each half-line
`(-∞, T]` meets it in a finite set) and the Rayleigh variational min–max principle yields
infinitely many eigenvalues, then the eigenvalue counting function `T ↦ #(S ∩ (-∞, T])`
tends to `+∞` as `T → +∞`.

This is the qualitative input to a Weyl law: the counting function is unbounded, so the
asymptotics of `counting S` are asymptotics of a divergent quantity.

The proof is elementary: given `k`, the infiniteness hypothesis provides `k` distinct
spectral points (`Set.Infinite.exists_subset_card_eq`); all of them lie below some bound
`M` (`Finset.exists_le`), hence `counting S T ≥ k` for every `T ≥ M`
(`Set.ncard_le_ncard`, using discreteness for finiteness of the ambient set). -/
