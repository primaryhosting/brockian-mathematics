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

/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term : Type
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

namespace Term

/-- Lifting of a renaming under a binder. -/

theorem subst_subst1 (σ : Nat → Term) (t s : Term) :
    subst σ (subst1 t s) = subst1 (subst σ t) (subst (up σ) s) := by
  simp only [subst1, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ m =>
      simp only [cons, up, subst_rename]
      exact (subst_id (σ m)).symm

/-! ### Parallel β-reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Term → Term → Prop
  | var (n : Nat) : Par (var n) (var n)
  | app {s s' t t' : Term} : Par s s' → Par t t' → Par (app s t) (app s' t')
  | lam {t t' : Term} : Par t t' → Par (lam t) (lam t')
  | beta {s s' t t' : Term} : Par s s' → Par t t' → Par (app (lam s) t) (subst1 t' s')

