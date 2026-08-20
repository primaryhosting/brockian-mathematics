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

set_option grind.warning false

/-!
# The diamond property of parallel β-reduction

We formalise untyped λ-terms in de Bruijn representation, define one-step
*parallel* β-reduction `CS.Par`, and prove that it has the diamond property
(`CS.church_rosser_beta_diamond`), which is the key combinatorial step in the
Church–Rosser theorem.  The proof follows Takahashi: we define the *complete
development* `CS.dev` of a term and show the triangle property
`Par a b → Par b (dev a)`.
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Tm : Type
  | var : ℕ → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  deriving DecidableEq

/-- `shift k t` increments every free variable of `t` with index `≥ k` by one. -/

theorem subst_shift_same (t : Tm) : ∀ (i : ℕ) (s : Tm), subst (shift i t) i s = t := by
  induction t with
  | var n =>
      intro i s
      simp only [shift, subst]
      split_ifs <;> first | rfl | (congr 1; omega)
  | app a b iha ihb => intro i s; simp only [shift, subst, iha, ihb]
  | lam a ih => intro i s; simp only [shift, subst, ih]

/-- Commuting a `shift` with a small cutoff past a substitution. -/
