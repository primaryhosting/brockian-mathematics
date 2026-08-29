/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term : Type
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

namespace Term

/-- Lift a renaming under a binder. -/
def upr (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => r n + 1

/-- Apply a renaming of variables to a term. -/
def ren (r : Nat → Nat) : Term → Term
  | var n => var (r n)
  | app a b => app (ren r a) (ren r b)
  | lam a => lam (ren (upr r) a)

/-- Lift a substitution under a binder. -/
def up (s : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => ren Nat.succ (s n)

/-- Apply a (parallel) substitution to a term. -/
def sub (s : Nat → Term) : Term → Term
  | var n => s n
  | app a b => app (sub s a) (sub s b)
  | lam a => lam (sub (up s) a)

/-- Extend a substitution with a new term for the index `0`. -/
def scons (u : Term) (s : Nat → Term) : Nat → Term
  | 0 => u
  | n + 1 => s n

/-- Single β-substitution: `a[b]`. -/
def subst1 (a b : Term) : Term := sub (scons b var) a

@[simp] theorem ren_var (r : Nat → Nat) (n : Nat) : ren r (var n) = var (r n) := rfl
@[simp] theorem ren_app (r : Nat → Nat) (a b : Term) :
    ren r (app a b) = app (ren r a) (ren r b) := rfl
@[simp] theorem ren_lam (r : Nat → Nat) (a : Term) : ren r (lam a) = lam (ren (upr r) a) := rfl
@[simp] theorem sub_var (s : Nat → Term) (n : Nat) : sub s (var n) = s n := rfl
@[simp] theorem sub_app (s : Nat → Term) (a b : Term) :
    sub s (app a b) = app (sub s a) (sub s b) := rfl
@[simp] theorem sub_lam (s : Nat → Term) (a : Term) : sub s (lam a) = lam (sub (up s) a) := rfl

theorem upr_comp (r₁ r₂ : Nat → Nat) : upr r₂ ∘ upr r₁ = upr (r₂ ∘ r₁) := by
  funext n; cases n <;> rfl

theorem ren_ren (r₁ r₂ : Nat → Nat) (t : Term) : ren r₂ (ren r₁ t) = ren (r₂ ∘ r₁) t := by
  induction t generalizing r₁ r₂ with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, upr_comp]

theorem up_comp_upr (s : Nat → Term) (r : Nat → Nat) : up s ∘ upr r = up (s ∘ r) := by
  funext n; cases n <;> rfl

theorem sub_ren (s : Nat → Term) (r : Nat → Nat) (t : Term) : sub s (ren r t) = sub (s ∘ r) t := by
  induction t generalizing s r with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, up_comp_upr]

theorem ren_up (r : Nat → Nat) (s : Nat → Term) :
    (fun n => ren (upr r) (up s n)) = up (fun n => ren r (s n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [up, ren_ren]; rfl

theorem ren_sub (r : Nat → Nat) (s : Nat → Term) (t : Term) :
    ren r (sub s t) = sub (fun n => ren r (s n)) t := by
  induction t generalizing r s with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, ren_up]

theorem sub_up (s₁ s₂ : Nat → Term) :
    (fun n => sub (up s₂) (up s₁ n)) = up (fun n => sub s₂ (s₁ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [up, sub_ren, ren_sub]; rfl

theorem sub_sub (s₁ s₂ : Nat → Term) (t : Term) :
    sub s₂ (sub s₁ t) = sub (fun n => sub s₂ (s₁ n)) t := by
  induction t generalizing s₁ s₂ with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, sub_up]

theorem sub_var_id (t : Term) : sub var t = t := by
  induction t with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih =>
      have : up var = var := by funext n; cases n <;> rfl
      simp [this, ih]

/-- Renaming commutes with single substitution. -/
theorem ren_subst1 (r : Nat → Nat) (a b : Term) :
    ren r (subst1 a b) = subst1 (ren (upr r) a) (ren r b) := by
  unfold subst1
  rw [ren_sub, sub_ren]
  congr 1
  funext n
  cases n <;> rfl

/-- A substitution commutes with single substitution. -/
theorem sub_subst1 (s : Nat → Term) (a b : Term) :
    sub s (subst1 a b) = subst1 (sub (up s) a) (sub s b) := by
  unfold subst1
  rw [sub_sub, sub_sub]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      have h1 : (scons (sub s b) var) ∘ Nat.succ = var := by funext m; rfl
      show s n = sub (scons (sub s b) var) (ren Nat.succ (s n))
      rw [sub_ren, h1, sub_var_id]

/-- One-step parallel β-reduction. -/
inductive Par : Term → Term → Prop
  | var (n : Nat) : Par (var n) (var n)
  | app {a a' b b' : Term} : Par a a' → Par b b' → Par (app a b) (app a' b')
  | lam {a a' : Term} : Par a a' → Par (lam a) (lam a')
  | beta {a a' b b' : Term} : Par a a' → Par b b' → Par (app (lam a) b) (subst1 a' b')

@[refl] theorem Par.refl (t : Term) : Par t t := by
  induction t with
  | var n => exact Par.var n
  | app a b iha ihb => exact iha.app ihb
  | lam a ih => exact ih.lam

theorem Par.lam_inv {a t : Term} (h : Par (Term.lam a) t) :
    ∃ a', t = Term.lam a' ∧ Par a a' := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

/-- Parallel reduction is stable under renaming. -/
theorem Par.ren {a b : Term} (h : Par a b) (r : Nat → Nat) : Par (Term.ren r a) (Term.ren r b) := by
  induction h generalizing r with
  | var n => exact Par.var _
  | app _ _ iha ihb => exact (iha r).app (ihb r)
  | lam _ ih => exact (ih _).lam
  | beta _ _ iha ihb =>
      rw [ren_subst1]
      exact Par.beta (iha _) (ihb r)

/-- Parallel reduction is stable under parallel substitution. -/
theorem Par.sub {a b : Term} (h : Par a b) {s s' : Nat → Term} (hs : ∀ n, Par (s n) (s' n)) :
    Par (Term.sub s a) (Term.sub s' b) := by
  induction h generalizing s s' with
  | var n => exact hs n
  | app _ _ iha ihb => exact (iha hs).app (ihb hs)
  | lam _ ih =>
      refine Par.lam (ih ?_)
      intro n
      cases n with
      | zero => exact Par.var 0
      | succ n => exact (hs n).ren Nat.succ
  | beta _ _ iha ihb =>
      rw [sub_subst1]
      refine Par.beta (iha ?_) (ihb hs)
      intro n
      cases n with
      | zero => exact Par.var 0
      | succ n => exact (hs n).ren Nat.succ

theorem Par.subst1 {a a' b b' : Term} (ha : Par a a') (hb : Par b b') :
    Par (Term.subst1 a b) (Term.subst1 a' b') := by
  refine ha.sub ?_
  intro n
  cases n with
  | zero => exact hb
  | succ n => exact Par.var n

/-- Ordinary one-step β-reduction (contract a single redex, anywhere in the term). -/
inductive Step : Term → Term → Prop
  | beta (a b : Term) : Step (app (lam a) b) (subst1 a b)
  | appL {a a' b : Term} : Step a a' → Step (app a b) (app a' b)
  | appR {a b b' : Term} : Step b b' → Step (app a b) (app a b')
  | lam {a a' : Term} : Step a a' → Step (lam a) (lam a')

/-- Reflexive-transitive closure of β-reduction. -/
inductive Steps : Term → Term → Prop
  | refl (a : Term) : Steps a a
  | tail {a b c : Term} : Steps a b → Step b c → Steps a c

theorem Steps.trans {a b c : Term} (h₁ : Steps a b) (h₂ : Steps b c) : Steps a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact ih.tail hs

theorem Steps.lam_congr {a a' : Term} (h : Steps a a') : Steps (Term.lam a) (Term.lam a') := by
  induction h with
  | refl => exact Steps.refl _
  | tail _ hs ih => exact ih.tail hs.lam

theorem Steps.appL_congr {a a' b : Term} (h : Steps a a') :
    Steps (Term.app a b) (Term.app a' b) := by
  induction h with
  | refl => exact Steps.refl _
  | tail _ hs ih => exact ih.tail hs.appL

theorem Steps.appR_congr {a b b' : Term} (h : Steps b b') :
    Steps (Term.app a b) (Term.app a b') := by
  induction h with
  | refl => exact Steps.refl _
  | tail _ hs ih => exact ih.tail hs.appR

/-- Every ordinary β-step is a parallel step. -/
theorem Step.toPar {a b : Term} (h : Step a b) : Par a b := by
  induction h with
  | beta a b => exact Par.beta (Par.refl a) (Par.refl b)
  | appL _ ih => exact ih.app (Par.refl _)
  | appR _ ih => exact (Par.refl _).app ih
  | lam _ ih => exact ih.lam

/-- Every parallel step is a finite sequence of ordinary β-steps. -/
theorem Par.toSteps {a b : Term} (h : Par a b) : Steps a b := by
  induction h with
  | var n => exact Steps.refl _
  | app _ _ iha ihb => exact (Steps.appL_congr iha).trans (Steps.appR_congr ihb)
  | lam _ ih => exact Steps.lam_congr ih
  | beta _ _ iha ihb =>
      exact ((Steps.appL_congr (Steps.lam_congr iha)).trans
        (Steps.appR_congr ihb)).tail (Step.beta _ _)

/-- Takahashi's complete development: contract all β-redexes present in the term. -/
def cd : Term → Term
  | var n => var n
  | app (lam a) b => subst1 (cd a) (cd b)
  | app a b => app (cd a) (cd b)
  | lam a => lam (cd a)

@[simp] theorem cd_var (n : Nat) : cd (var n) = var n := rfl
@[simp] theorem cd_lam (a : Term) : cd (lam a) = lam (cd a) := rfl
@[simp] theorem cd_app_lam (a b : Term) : cd (app (lam a) b) = subst1 (cd a) (cd b) := rfl
@[simp] theorem cd_app_var (n : Nat) (b : Term) : cd (app (var n) b) = app (var n) (cd b) := rfl
@[simp] theorem cd_app_app (a₁ a₂ b : Term) :
    cd (app (app a₁ a₂) b) = app (cd (app a₁ a₂)) (cd b) := rfl

/-- The key "triangle" property: every parallel reduct of `a` parallel-reduces to the
complete development of `a`. -/
theorem Par.triangle {a b : Term} (h : Par a b) : Par b (cd a) := by
  induction h with
  | var n => exact Par.var n
  | @app a a' b b' ha _ iha ihb =>
      cases a with
      | var n =>
          cases ha with
          | var n => exact (Par.var n).app ihb
      | app a₁ a₂ => exact iha.app ihb
      | lam c =>
          obtain ⟨c', rfl, _⟩ := ha.lam_inv
          obtain ⟨d, hd, hcd⟩ := iha.lam_inv
          rw [cd_lam] at hd
          cases hd
          exact Par.beta hcd ihb
  | lam _ ih => exact ih.lam
  | @beta a a' b b' _ _ iha ihb =>
      rw [cd_app_lam]
      exact Par.subst1 iha ihb

/-- The diamond property of parallel reduction. -/
theorem Par.diamond {a b c : Term} (hb : Par a b) (hc : Par a c) :
    ∃ d, Par b d ∧ Par c d :=
  ⟨cd a, hb.triangle, hc.triangle⟩

/-- Reflexive-transitive closure of parallel reduction. -/
inductive Pars : Term → Term → Prop
  | refl (a : Term) : Pars a a
  | tail {a b c : Term} : Pars a b → Par b c → Pars a c

theorem Pars.strip {a b c : Term} (hb : Par a b) (hc : Pars a c) :
    ∃ d, Pars b d ∧ Par c d := by
  induction hc with
  | refl => exact ⟨b, Pars.refl b, hb⟩
  | tail _ hstep ih =>
      obtain ⟨d₁, hbd₁, hcd₁⟩ := ih
      obtain ⟨d, hd₁, hd₂⟩ := hcd₁.diamond hstep
      exact ⟨d, hbd₁.tail hd₁, hd₂⟩

/-- Confluence of the reflexive-transitive closure of parallel reduction. -/
theorem Pars.confluent {a b c : Term} (hb : Pars a b) (hc : Pars a c) :
    ∃ d, Pars b d ∧ Pars c d := by
  induction hb with
  | refl => exact ⟨c, hc, Pars.refl c⟩
  | tail _ hstep ih =>
      obtain ⟨d₁, hbd₁, hcd₁⟩ := ih
      obtain ⟨d, hd₁, hd₂⟩ := Pars.strip hstep hbd₁
      exact ⟨d, hd₁, hcd₁.tail hd₂⟩

theorem Steps.toPars {a b : Term} (h : Steps a b) : Pars a b := by
  induction h with
  | refl => exact Pars.refl _
  | tail _ hs ih => exact ih.tail hs.toPar

theorem Pars.toSteps {a b : Term} (h : Pars a b) : Steps a b := by
  induction h with
  | refl => exact Steps.refl _
  | tail _ hs ih => exact ih.trans hs.toSteps

end Term

/-- **Church–Rosser theorem for β-reduction**: `→β*` is confluent. -/
theorem church_rosser_beta {a b c : Term} (hb : Term.Steps a b) (hc : Term.Steps a c) :
    ∃ d, Term.Steps b d ∧ Term.Steps c d := by
  obtain ⟨d, h₁, h₂⟩ := hb.toPars.confluent hc.toPars
  exact ⟨d, h₁.toSteps, h₂.toSteps⟩

/-- **Church–Rosser / diamond property for parallel β-reduction.**
If a λ-term `a` parallel-reduces in one step to both `b` and `c`, then `b` and `c` have a
common one-step parallel reduct. -/
theorem church_rosser_beta_diamond {a b c : Term} (hb : Term.Par a b) (hc : Term.Par a c) :
    ∃ d, Term.Par b d ∧ Term.Par c d :=
  ⟨Term.cd a, hb.triangle, hc.triangle⟩

end CS

namespace CS

section Sanity

open Term

/-- Sanity check: `(λ x. x) y` β-reduces to `y`. -/
example : Par (app (lam (var 0)) (var 1)) (var 1) := by
  have h := Par.beta (Par.var 0) (Par.var 1)
  simpa [subst1, sub, scons] using h

/-- Sanity check: `Par` is not the trivial relation. -/
example : ¬ Par (var 0) (var 1) := by
  intro h
  cases h

end Sanity

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

