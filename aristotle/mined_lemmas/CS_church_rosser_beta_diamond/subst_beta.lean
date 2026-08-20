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

theorem subst_beta (sigma : ℕ → Lam) (s t : Lam) :
    subst sigma (subst (beta s) t) = subst (beta (subst sigma s)) (subst (up sigma) t) := by
  rw [subst_subst, subst_subst]
  refine subst_ext ?_ t
  intro n
  cases n with
  | zero => simp [beta, subst, up]
  | succ n =>
      simp only [beta, subst, up, subst_rename]
      exact (subst_id _).symm

/-! ### Parallel β-reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Lam → Lam → Prop
  | var (n : ℕ) : Par (.var n) (.var n)
  | app {a a' b b' : Lam} : Par a a' → Par b b' → Par (.app a b) (.app a' b')
  | lam {t t' : Lam} : Par t t' → Par (.lam t) (.lam t')
  | beta {t t' s s' : Lam} : Par t t' → Par s s' →
      Par (.app (.lam t) s) (subst (beta s') t')

