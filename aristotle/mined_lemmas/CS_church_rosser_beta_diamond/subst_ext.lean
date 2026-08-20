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

theorem subst_ext {sigma tau : ℕ → Lam} (h : ∀ n, sigma n = tau n) (t : Lam) :
    subst sigma t = subst tau t := by
  induction t generalizing sigma tau with
  | var n => simp [subst, h]
  | app a b iha ihb => simp [subst, iha h, ihb h]
  | lam t ih =>
      refine congrArg Lam.lam (ih ?_)
      intro n; cases n <;> simp [up, h]

