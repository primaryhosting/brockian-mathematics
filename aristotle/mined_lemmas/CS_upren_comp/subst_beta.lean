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

theorem subst_beta (σ : ℕ → Term) (a b : Term) :
    subst σ (beta b a) = beta (subst σ b) (subst (upsub σ) a) := by
  unfold beta
  rw [subst_subst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ m =>
      show σ m = subst (scons (subst σ b) Term.var) (ren Nat.succ (σ m))
      rw [subst_ren]
      exact (subst_var (σ m)).symm

/-! ### Parallel reduction -/

/-- One-step parallel β-reduction. -/
inductive Pstep : Term → Term → Prop where
  | var (n : ℕ) : Pstep (.var n) (.var n)
  | app {s s' t t' : Term} : Pstep s s' → Pstep t t' → Pstep (.app s t) (.app s' t')
  | lam {s s' : Term} : Pstep s s' → Pstep (.lam s) (.lam s')
  | beta {s s' t t' : Term} : Pstep s s' → Pstep t t' → Pstep (.app (.lam s) t) (beta t' s')

