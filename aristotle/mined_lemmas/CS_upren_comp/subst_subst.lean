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

theorem subst_subst (τ σ : ℕ → Term) (s : Term) :
    subst τ (subst σ s) = subst (fun n => subst τ (σ n)) s := by
  induction s generalizing τ σ with
  | var n => rfl
  | app a b iha ihb => simp [subst, iha, ihb]
  | lam a ih =>
      have h : (fun n => subst (upsub τ) (upsub σ n)) = upsub (fun n => subst τ (σ n)) := by
        funext n
        cases n with
        | zero => rfl
        | succ m =>
            show subst (upsub τ) (ren Nat.succ (σ m)) = ren Nat.succ (subst τ (σ m))
            rw [subst_ren, ren_subst]
            rfl
      simp [subst, ih, h]

