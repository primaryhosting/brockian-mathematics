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

theorem Pstep.triangle {s t : Term} (h : Pstep s t) : Pstep t (cd s) := by
  induction h with
  | var n => exact Pstep.var n
  | @app a a' b b' hab _ iha ihb =>
      cases a with
      | var n => rw [cd_app_var]; exact Pstep.app iha ihb
      | app c d => rw [cd_app_app]; exact Pstep.app iha ihb
      | lam c =>
          obtain ⟨c', rfl, _⟩ := hab.lam_inv
          rw [cd_app_lam]
          obtain ⟨e, he, hce⟩ := iha.lam_inv
          have hcd : cd (Term.lam c) = Term.lam (cd c) := rfl
          rw [hcd] at he
          have he' : cd c = e := by injection he
          subst he'
          exact Pstep.beta hce ihb
  | lam _ ih => exact Pstep.lam ih
  | @beta a a' b b' _ _ iha ihb =>
      rw [cd_app_lam]
      exact Pstep.beta_congr iha ihb

/-- **Diamond property of parallel β-reduction.**  If a λ-term `s` reduces in one
parallel β-step to both `t` and `u`, then `t` and `u` have a common one-step
parallel reduct. -/
