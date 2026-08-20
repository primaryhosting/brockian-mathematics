import Mathlib

/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
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

set_option grind.warning false

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term where
  | var : ℕ → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

/-- Lifting a renaming under a binder. -/

def subst (σ : ℕ → Term) : Term → Term
  | .var n => σ n
  | .app s t => .app (subst σ s) (subst σ t)
  | .lam s => .lam (subst (upsub σ) s)

/-- Extending a substitution with a new term for the index `0`. -/
