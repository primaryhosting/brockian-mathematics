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

theorem shift_subst_ge (t : Tm) : ∀ (i j : ℕ) (s : Tm), i ≤ j →
    shift i (subst t j s) = subst (shift i t) (j + 1) (shift i s) := by
  induction t with
  | var n =>
      intro i j s hij
      simp only [shift, subst]
      split_ifs <;>
        first | rfl | (simp only [shift]; split_ifs <;> first | rfl | (congr 1; omega))
              | omega
  | app a b iha ihb =>
      intro i j s hij; simp only [shift, subst, iha i j s hij, ihb i j s hij]
  | lam a ih =>
      intro i j s hij
      simp only [shift, subst]
      rw [ih (i + 1) (j + 1) (shift 0 s) (by omega), shift_shift s 0 i (Nat.zero_le i)]

/-- Commuting a `shift` with a large cutoff past a substitution. -/
