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


theorem betas_of_par_star {a b : Tm} (h : ReflTransGen Par a b) : Betas a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans hstep.toBetas

/-- **Church–Rosser theorem for β-reduction.** If `a` β-reduces in many steps to both `b`
and `c`, then `b` and `c` β-reduce in many steps to a common term. -/
