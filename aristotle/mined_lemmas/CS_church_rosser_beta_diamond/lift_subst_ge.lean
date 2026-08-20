import RequestProject.ChurchRosser
import Mathlib.Logic.Relation

/-!
# Confluence of β-reduction

Building on the diamond property of one-step parallel β-reduction
(`CS.church_rosser_beta_diamond`), we derive the Church–Rosser theorem for ordinary
β-reduction: the reflexive transitive closure of the one-step β-reduction relation is
confluent.

The abstract step from a diamond-like property to confluence of the transitive closure is
Mathlib's `Relation.church_rosser`.
-/

namespace CS
namespace Tm

open Relation

/-- Ordinary one-step β-reduction: contract a single β-redex anywhere in the term. -/
inductive Beta : Tm → Tm → Prop
  | beta (a b : Tm) : Beta (app (lam a) b) (subst a 0 b)
  | appl {a a' b : Tm} : Beta a a' → Beta (app a b) (app a' b)
  | appr {a b b' : Tm} : Beta b b' → Beta (app a b) (app a b')
  | lam {a a' : Tm} : Beta a a' → Beta (lam a) (lam a')

/-- Many-step β-reduction. -/
abbrev Betas : Tm → Tm → Prop := ReflTransGen Beta


theorem lift_subst_ge (t : Tm) :
    ∀ i n u, n ≤ i → lift i (subst t n u) = subst (lift (i + 1) t) n (lift i u) := by
  induction t with
  | var k => intro i n u h; var_case
  | app a b iha ihb => intro i n u h; simp [lift, subst, iha i n u h, ihb i n u h]
  | lam a ih =>
      intro i n u h
      simp [lift, subst, ih (i + 1) (n + 1) (lift 0 u) (by omega),
        lift_lift u 0 i (Nat.zero_le i)]

/-- The substitution lemma. -/
