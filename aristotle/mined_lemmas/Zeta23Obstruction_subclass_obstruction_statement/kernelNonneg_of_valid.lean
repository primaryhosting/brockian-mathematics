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

theorem kernelNonneg_of_valid (C : Certificate n) (i : Fin n)
    (hw : 0 < C.weight i) (hV : Valid C) : KernelNonneg C := by
  intro x
  have h := hV (fun _ => x) i
  exact nonneg_of_mul_nonneg_right h hw

/-!
## The subclass obstruction

Fixed kernel + pointwise discard + one bad deep value ⟹ the certificate is
invalid, and it already fails on an explicit deep-pair configuration.
-/

/-- **Abstract subclass obstruction.**  Let `C` be a fixed-kernel
pointwise-discard linear certificate over finitely many species, and let
`i ≠ j` be two species carrying strictly positive charging weights.  If the
(analytically continued) kernel takes a negative value at some deep point `z₀`
— the repaired witness — then there is a *deep-pair configuration* at `z₀` for
`i` and `j` on which

* the termwise (pointwise-discard) bound fails at both species of the pair,
* hence the termwise bound fails outright,
* and the total linear charge of the certificate is strictly negative;

consequently the certificate is invalid and its kernel-positivity hypothesis
`h_pos` cannot hold. -/
