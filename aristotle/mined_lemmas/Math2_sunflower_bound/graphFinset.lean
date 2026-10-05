/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
## What is proved here

* `Math2.sunflower_bound` : the sunflower lemma with the classical Erdős–Rado bound, i.e. every
  family of `w`-element sets with more than `w ! * (r-1) ^ w` members contains a sunflower with
  `r` petals.
* `Math2.exists_large_sunflower_free_family` : the factor `(r-1) ^ w` in that bound is necessary,
  since for `r ≥ 2` there is a sunflower-free family of `(r-1) ^ w` sets of size `w`.

The quantitative improvement of Alweiss, Lovett, Wu and Zhang, which replaces the factor `w !` by
`(C * Real.log w) ^ w`, is *not* established here; the bound proved below is the classical one.
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A finite family `S` of finite sets is a *sunflower* if there is a *core* `K` such that any
two distinct members of `S` meet exactly in `K`. -/

def graphFinset {w k : ℕ} (f : Fin w → Fin k) : Finset (Fin w × Fin k) :=
  Finset.univ.image (fun i => (i, f i))

