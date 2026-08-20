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


theorem beta_confluent {a b c : Tm} (hab : Betas a b) (hac : Betas a c) :
    ∃ d, Betas b d ∧ Betas c d := by
  have hab' : ReflTransGen Par a b := hab.mono fun _ _ h => h.toPar
  have hac' : ReflTransGen Par a c := hac.mono fun _ _ h => h.toPar
  obtain ⟨d, hbd, hcd⟩ :=
    Relation.church_rosser
      (fun _ _ _ h₁ h₂ => by
        obtain ⟨w, hw₁, hw₂⟩ := church_rosser_beta_diamond h₁ h₂
        exact ⟨w, .single hw₁, .single hw₂⟩)
      hab' hac'
  exact ⟨d, betas_of_par_star hbd, betas_of_par_star hcd⟩

end Tm
end CS

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Statement: One-step parallel β-reduction in the λ-calculus has the diamond property.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Tm : Type
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  deriving DecidableEq

namespace Tm

/-- `lift i t` increments every free variable of `t` whose index is `≥ i`. -/
