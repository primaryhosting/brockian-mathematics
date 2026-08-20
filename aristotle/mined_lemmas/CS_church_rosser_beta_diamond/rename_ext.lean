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

theorem rename_ext {xi zeta : ℕ → ℕ} (h : ∀ n, xi n = zeta n) (t : Lam) :
    rename xi t = rename zeta t := by
  induction t generalizing xi zeta with
  | var n => simp [rename, h]
  | app a b iha ihb => simp [rename, iha h, ihb h]
  | lam t ih =>
      refine congrArg Lam.lam (ih ?_)
      intro n; cases n <;> simp [upr, h]

