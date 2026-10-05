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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000

namespace Brockian.Weyl.WeylLawTarget

variable {ι : Type*}

/-- The eigenvalue counting function of a spectrum.

`lam : ι → ℝ` is the eigenvalue list, indexed by `ι` and repeated according to
multiplicity, and `counting lam Λ` is the number of eigenvalues that are `≤ Λ`,
counted with multiplicity.  (This is the function `N(Λ)` appearing in Weyl's law.) -/

def DiscreteSpectrum (lam : ι → ℝ) : Prop := ∀ Λ : ℝ, {i | lam i ≤ Λ}.Finite

/-- **RVM** (Rayleigh Variational Minimax): the spectrum admits a min–max enumeration.

That is, the Rayleigh–Ritz min–max principle over an infinite-dimensional form domain
produces an injective enumeration `e : ℕ → ι` of (part of) the eigenvalue list along
which the eigenvalues `k ↦ lam (e k)` are nondecreasing.  In particular the spectrum
contains infinitely many eigenvalues, counted with multiplicity. -/
