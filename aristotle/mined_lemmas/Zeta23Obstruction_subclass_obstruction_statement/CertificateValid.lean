/-
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-- A **configuration** of deep points: finitely many species, each carrying a real
"deep point" `pt i` and a strictly positive weight `wt i`. -/
structure DeepConfig where
  /-- number of species -/
  n : ℕ
  /-- the deep point attached to each species -/
  pt : Fin n → ℝ
  /-- the (strictly positive) weight attached to each species -/
  wt : Fin n → ℝ
  /-- positivity of the weights -/
  wt_pos : ∀ i : Fin n, 0 < wt i

/-- The **linear charge** of a configuration relative to a fixed kernel `R`:
the linear functional `c ↦ ∑ᵢ wᵢ · R(zᵢ)` obtained by per-species linear charging. -/

def CertificateValid (R σ : ℝ → ℝ) : Prop :=
  ∀ (z a b : ℝ) (ha : 0 < a) (hb : 0 < b), TermwiseNonneg R (deepPair σ z a b ha hb)

/-- **Abstract subclass obstruction.**

A certificate in this subclass is determined by a *fixed* kernel `R : ℝ → ℝ`, symmetric
under the reflection `σ` pairing deep points, and it is used only through pointwise
discard plus per-species linear charging.  If the (analytically continued) kernel takes a
single negative value `R z < 0` at some deep point `z` — the repaired witness — then the
deep-pair configuration at `z` defeats the certificate: for *every* choice of positive
species weights the termwise bound fails and the linear charge is strictly negative.
Consequently no such certificate is valid. -/
