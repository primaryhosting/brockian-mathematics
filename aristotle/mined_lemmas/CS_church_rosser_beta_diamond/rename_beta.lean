/-
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Lam where
  | var : ℕ → Lam
  | app : Lam → Lam → Lam
  | lam : Lam → Lam
  deriving DecidableEq

namespace Lam

/-- Lifting a renaming under a binder. -/

theorem rename_beta (xi : ℕ → ℕ) (s t : Lam) :
    rename xi (subst (beta s) t) = subst (beta (rename xi s)) (rename (upr xi) t) := by
  rw [rename_subst, subst_rename]
  refine subst_ext ?_ t
  intro n; cases n <;> simp [beta, upr, rename]

/-- Substitution commutes with a β-substitution. -/
