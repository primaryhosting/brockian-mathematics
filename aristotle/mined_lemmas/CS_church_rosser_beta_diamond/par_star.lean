/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Trm : Type
  | var : Nat → Trm
  | app : Trm → Trm → Trm
  | lam : Trm → Trm
  deriving DecidableEq

namespace Trm

/-- Lifting a renaming under a binder. -/

theorem par_star {t u : Trm} (h : Par t u) : Par u (star t) := by
  induction h with
  | var i => exact Par.var i
  | lam _ ih => exact Par.lam ih
  | @app a a' b b' ha _ iha ihb =>
    cases a with
    | var i =>
      cases ha
      exact Par.app (Par.var i) ihb
    | app a₁ a₂ => exact Par.app iha ihb
    | lam c =>
      cases ha with
      | lam hc =>
        rename_i c'
        have : Par (Trm.lam c') (Trm.lam (star c)) := iha
        cases this with
        | lam hc' => exact Par.beta hc' ihb
  | @beta a a' b b' _ _ iha ihb => exact Par.sub1 iha ihb

/-! ### Sanity checks -/

/-- `(λ x. x) t` parallel-reduces to `t`. -/
example (t : Trm) : Par (app (lam (var 0)) t) t := Par.beta (Par.refl _) (Par.refl _)

/-- `(λ x. λ y. x) t` parallel-reduces to `λ y. t` (with `t` shifted under the binder). -/
example (t : Trm) : Par (app (lam (lam (var 1))) t) (lam (rename Nat.succ t)) :=
  Par.beta (Par.refl _) (Par.refl _)

/-! ### Ordinary β-reduction, and confluence -/

/-- One-step β-reduction. -/
inductive Beta : Trm → Trm → Prop
  | beta (a b : Trm) : Beta (app (lam a) b) (sub1 a b)
  | appL {a a' : Trm} (b : Trm) : Beta a a' → Beta (app a b) (app a' b)
  | appR (a : Trm) {b b' : Trm} : Beta b b' → Beta (app a b) (app a b')
  | lam {a a' : Trm} : Beta a a' → Beta (lam a) (lam a')

/-- Reflexive-transitive closure of β-reduction. -/
inductive Betas : Trm → Trm → Prop
  | refl (a : Trm) : Betas a a
  | tail {a b c : Trm} : Betas a b → Beta b c → Betas a c

/-- Reflexive-transitive closure of parallel β-reduction. -/
inductive Pars : Trm → Trm → Prop
  | refl (a : Trm) : Pars a a
  | tail {a b c : Trm} : Pars a b → Par b c → Pars a c

