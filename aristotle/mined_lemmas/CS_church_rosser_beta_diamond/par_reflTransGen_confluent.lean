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

theorem par_reflTransGen_confluent {a b c : Tm}
    (hb : Relation.ReflTransGen Par a b) (hc : Relation.ReflTransGen Par a c) :
    ∃ d, Relation.ReflTransGen Par b d ∧ Relation.ReflTransGen Par c d := by
  obtain ⟨d, h1, h2⟩ :=
    Relation.church_rosser
      (fun _ _ _ h1 h2 => by
        obtain ⟨d, hd1, hd2⟩ := church_rosser_beta_diamond h1 h2
        exact ⟨d, Relation.ReflGen.single hd1, Relation.ReflTransGen.single hd2⟩)
      hb hc
  exact ⟨d, h1, h2⟩

/-! ### Church–Rosser for ordinary β-reduction -/

/-- Ordinary one-step β-reduction: contract a single β-redex anywhere in a term. -/
inductive Beta : Tm → Tm → Prop
  | beta (a b : Tm) : Beta (.app (.lam a) b) (subst a 0 b)
  | appL {a a' : Tm} (b : Tm) : Beta a a' → Beta (.app a b) (.app a' b)
  | appR (a : Tm) {b b' : Tm} : Beta b b' → Beta (.app a b) (.app a b')
  | lam {a a' : Tm} : Beta a a' → Beta (.lam a) (.lam a')

/-- Multi-step β-reduction. -/
abbrev Betas : Tm → Tm → Prop := Relation.ReflTransGen Beta

