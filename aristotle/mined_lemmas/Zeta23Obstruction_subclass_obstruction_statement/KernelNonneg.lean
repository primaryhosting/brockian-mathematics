import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-!
## An abstract finite-dimensional model of a fixed-kernel pointwise-discard certificate

We model the "certificate chain" abstractly.  There are finitely many *species*
(indexed by `Fin n`), each carrying a nonnegative *weight*.  A *configuration*
assigns to each species a *deep point* of the real line.  The certificate is
built from one *fixed kernel* `R : ℝ → ℝ`: the charge attached to a
configuration is the linear functional

`charge C z = ∑ i, weight i * R (z i)`,

and the *pointwise-discard* step of the chain is only legitimate when each
individual term is discarded upwards, i.e. when the termwise bound
`0 ≤ weight i * R (z i)` holds for every species and every configuration.
The content of the obstruction is purely about this quantifier structure: the
kernel is fixed *before* the configuration is chosen, so a single point `z₀`
with `R z₀ < 0` can be fed simultaneously to a pair of species, breaking the
termwise bound and even making the whole linear charge negative.
-/

/-- A *fixed-kernel pointwise-discard linear certificate* over `n` species:
a kernel `R : ℝ → ℝ`, chosen once and for all, together with nonnegative
per-species charging weights. -/
structure Certificate (n : ℕ) where
  /-- The fixed kernel used at every deep point. -/
  R : ℝ → ℝ
  /-- The per-species linear charging weights. -/
  weight : Fin n → ℝ
  /-- The weights are nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i

/-- A *configuration*: an assignment of a deep point to each species. -/
abbrev Config (n : ℕ) : Type := Fin n → ℝ

variable {n : ℕ}

/-- The linear charge attached by a certificate to a configuration. -/

def KernelNonneg (C : Certificate n) : Prop :=
  ∀ x : ℝ, 0 ≤ C.R x

/-- On a constant configuration the charge factors as total weight times the
kernel value. -/
