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

set_option autoImplicit false

/-!
# Parallel β-reduction has the diamond property

We formalize the untyped λ-calculus with de Bruijn indices, define parallel
one-step β-reduction `CS.Par`, and prove that it satisfies the diamond
property (Takahashi's method of complete developments).
-/

namespace CS

/-- λ-terms with de Bruijn indices. -/
inductive Term : Type
  | var : ℕ → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

namespace Term

/-- Lifting of a renaming under a binder. -/

theorem subst_inst (s : ℕ → Term) (t u : Term) :
    subst s (inst t u) = inst (subst (up s) t) (subst s u) := by
  unfold inst
  rw [subst_subst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show subst s (var n) = subst (cons (subst s u)) (ren Nat.succ (s n))
    rw [subst_ren]
    show s n = subst (fun m => cons (subst s u) (m + 1)) (s n)
    rw [show (fun m => cons (subst s u) (m + 1)) = var from rfl, subst_id]

end Term

open Term

/-- One-step parallel β-reduction. -/
inductive Par : Term → Term → Prop
  | var (n : ℕ) : Par (var n) (var n)
  | app {t t' u u' : Term} : Par t t' → Par u u' → Par (app t u) (app t' u')
  | lam {t t' : Term} : Par t t' → Par (lam t) (lam t')
  | beta {t t' u u' : Term} : Par t t' → Par u u' → Par (app (lam t) u) (inst t' u')

