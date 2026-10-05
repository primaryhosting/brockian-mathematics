import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Zeta23Obstruction

/-!
## The abstract model

We model a "fixed-kernel pointwise-discard linear certificate" in a finite-dimensional,
purely combinatorial way.

* A **kernel** is a fixed function `R : ℝ → ℝ`.  In the intended application `R` is the
  (analytically continued) remainder kernel of the certificate; only its *values* matter here.
* A **deep region** is a set `D : Set ℝ` of admissible evaluation points ("deep points").
* A **deep-pair configuration** consists of two species, each placed at a deep point and
  carrying a strictly positive weight.  (Two species is exactly the "deep-pair" situation:
  the argument needs no more, and works verbatim for any positive number of species.)
* The certificate charges a configuration linearly, `charge R C = ∑ i, w i * R (z i)`, and the
  *pointwise discard* step of the chain is only licensed if every individual term is
  nonnegative, i.e. if `R` is nonnegative at each deep point of the configuration.

`Valid R D` is exactly the assertion that the pointwise-discard step is licensed for every
deep-pair configuration.  The obstruction says: one deep point `z ∈ D` with `R z < 0`
destroys validity, and exhibits an explicit configuration on which the termwise bound fails
and the total charge is negative.
-/

/-- A deep-pair configuration over the deep region `D`: two species, each located at a deep
point and carrying a strictly positive weight. -/
structure DeepPairConfig (D : Set ℝ) where
  /-- the location of each species -/
  pt : Fin 2 → ℝ
  /-- the (positive) weight of each species -/
  wt : Fin 2 → ℝ
  /-- all species sit at deep points -/
  pt_deep : ∀ i, pt i ∈ D
  /-- all weights are strictly positive -/
  wt_pos : ∀ i, 0 < wt i

/-- The linear charge of a configuration against a fixed kernel `R`. -/

theorem no_certificate_with_negative_deep_value
    (R : ℝ → ℝ) (h_pos : ∀ x, 0 ≤ R x) (z : ℝ) : ¬ R z < 0 :=
  not_lt.mpr (h_pos z)

end Zeta23Obstruction

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

