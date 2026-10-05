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

/-- Lifting of a renaming under a binder. -/
def upr (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => r n + 1

/-- Renaming (variable-for-variable substitution). -/
def rename (r : Nat → Nat) : Term → Term
  | var n => var (r n)
  | app s t => app (rename r s) (rename r t)
  | lam t => lam (rename (upr r) t)

/-- Lifting of a substitution under a binder. -/
def up (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Parallel substitution. -/
def subst (σ : Nat → Term) : Term → Term
  | var n => σ n
  | app s t => app (subst σ s) (subst σ t)
  | lam t => lam (subst (up σ) t)

/-- The substitution replacing variable `0` by `t`. -/
def cons (t : Term) : Nat → Term
  | 0 => t
  | n + 1 => var n

/-- Substitution of a single term for the outermost bound variable. -/
def subst1 (t s : Term) : Term := subst (cons t) s

/-! ### Basic substitution calculus -/

@[simp] theorem rename_var (r : Nat → Nat) (n : Nat) : rename r (var n) = var (r n) := rfl
@[simp] theorem rename_app (r : Nat → Nat) (s t : Term) :
    rename r (app s t) = app (rename r s) (rename r t) := rfl
@[simp] theorem rename_lam (r : Nat → Nat) (t : Term) :
    rename r (lam t) = lam (rename (upr r) t) := rfl
@[simp] theorem subst_var (σ : Nat → Term) (n : Nat) : subst σ (var n) = σ n := rfl
@[simp] theorem subst_app (σ : Nat → Term) (s t : Term) :
    subst σ (app s t) = app (subst σ s) (subst σ t) := rfl
@[simp] theorem subst_lam (σ : Nat → Term) (t : Term) :
    subst σ (lam t) = lam (subst (up σ) t) := rfl

theorem rename_rename (r₁ r₂ : Nat → Nat) (s : Term) :
    rename r₂ (rename r₁ s) = rename (fun n => r₂ (r₁ n)) s := by
  induction s generalizing r₁ r₂ with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam t ih =>
      have h : (fun n => upr r₂ (upr r₁ n)) = upr (fun n => r₂ (r₁ n)) := by
        funext n; cases n <;> rfl
      simp only [rename_lam, ih, h]

theorem rename_id (s : Term) : rename id s = s := by
  induction s with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam t ih =>
      have : upr id = id := by funext n; cases n <;> rfl
      simp [this, ih]

theorem subst_rename (σ : Nat → Term) (r : Nat → Nat) (s : Term) :
    subst σ (rename r s) = subst (fun n => σ (r n)) s := by
  induction s generalizing σ r with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam t ih =>
      have h : (fun n => up σ (upr r n)) = up (fun n => σ (r n)) := by
        funext n; cases n <;> rfl
      simp only [rename_lam, subst_lam, ih, h]

theorem rename_subst (r : Nat → Nat) (σ : Nat → Term) (s : Term) :
    rename r (subst σ s) = subst (fun n => rename r (σ n)) s := by
  induction s generalizing σ r with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam t ih =>
      have h : (fun n => Term.rename (upr r) (up σ n)) = up (fun n => Term.rename r (σ n)) := by
        funext n
        cases n with
        | zero => rfl
        | succ m =>
            simp only [up, rename_rename]
            rfl
      simp only [rename_lam, subst_lam, ih, h]

theorem subst_subst (σ τ : Nat → Term) (s : Term) :
    subst τ (subst σ s) = subst (fun n => subst τ (σ n)) s := by
  induction s generalizing σ τ with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam t ih =>
      have h : (fun n => subst (up τ) (up σ n)) = up (fun n => subst τ (σ n)) := by
        funext n
        cases n with
        | zero => rfl
        | succ m =>
            simp only [up, subst_rename]
            exact (rename_subst _ _ _).symm
      simp only [subst_lam, ih, h]

theorem subst_id (s : Term) : subst var s = s := by
  induction s with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam t ih =>
      have : up var = var := by funext n; cases n <;> rfl
      simp [this, ih]

theorem rename_subst1 (r : Nat → Nat) (t s : Term) :
    rename r (subst1 t s) = subst1 (rename r t) (rename (upr r) s) := by
  simp only [subst1, rename_subst, subst_rename]
  congr 1
  funext n
  cases n <;> rfl

theorem subst_subst1 (σ : Nat → Term) (t s : Term) :
    subst σ (subst1 t s) = subst1 (subst σ t) (subst (up σ) s) := by
  simp only [subst1, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ m =>
      simp only [cons, up, subst_rename]
      exact (subst_id (σ m)).symm

/-! ### Parallel β-reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Term → Term → Prop
  | var (n : Nat) : Par (var n) (var n)
  | app {s s' t t' : Term} : Par s s' → Par t t' → Par (app s t) (app s' t')
  | lam {t t' : Term} : Par t t' → Par (lam t) (lam t')
  | beta {s s' t t' : Term} : Par s s' → Par t t' → Par (app (lam s) t) (subst1 t' s')

theorem Par.refl : ∀ s : Term, Par s s
  | Term.var n => Par.var n
  | Term.app s t => Par.app (Par.refl s) (Par.refl t)
  | Term.lam t => Par.lam (Par.refl t)

theorem Par.rename {s t : Term} (h : Par s t) (r : Nat → Nat) :
    Par (Term.rename r s) (Term.rename r t) := by
  induction h generalizing r with
  | var n => exact Par.var _
  | app _ _ ih₁ ih₂ => exact Par.app (ih₁ r) (ih₂ r)
  | lam _ ih => exact Par.lam (ih _)
  | beta _ _ ih₁ ih₂ =>
      rw [rename_subst1]
      exact Par.beta (ih₁ _) (ih₂ _)

theorem Par.up {σ τ : Nat → Term} (h : ∀ n, Par (σ n) (τ n)) :
    ∀ n, Par (Term.up σ n) (Term.up τ n) := by
  intro n
  cases n with
  | zero => exact Par.var 0
  | succ m => exact (h m).rename Nat.succ

theorem Par.subst {s t : Term} (h : Par s t) {σ τ : Nat → Term} (hσ : ∀ n, Par (σ n) (τ n)) :
    Par (Term.subst σ s) (Term.subst τ t) := by
  induction h generalizing σ τ with
  | var n => exact hσ n
  | app _ _ ih₁ ih₂ => exact Par.app (ih₁ hσ) (ih₂ hσ)
  | lam _ ih => exact Par.lam (ih (Par.up hσ))
  | beta _ _ ih₁ ih₂ =>
      rw [subst_subst1]
      exact Par.beta (ih₁ (Par.up hσ)) (ih₂ hσ)

theorem Par.cons {t t' : Term} (h : Par t t') : ∀ n, Par (Term.cons t n) (Term.cons t' n) := by
  intro n
  cases n with
  | zero => exact h
  | succ m => exact Par.var m

theorem Par.subst1 {s s' t t' : Term} (hs : Par s s') (ht : Par t t') :
    Par (Term.subst1 t s) (Term.subst1 t' s') :=
  hs.subst (Par.cons ht)

theorem Par.lam_inv {t u : Term} (h : Par (Term.lam t) u) :
    ∃ u', u = Term.lam u' ∧ Par t u' := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

/-- Ordinary one-step β-reduction, for reference. -/
inductive Beta : Term → Term → Prop
  | beta (s t : Term) : Beta (Term.app (Term.lam s) t) (subst1 t s)
  | appL {s s' : Term} (t : Term) : Beta s s' → Beta (Term.app s t) (Term.app s' t)
  | appR (s : Term) {t t' : Term} : Beta t t' → Beta (Term.app s t) (Term.app s t')
  | lam {t t' : Term} : Beta t t' → Beta (Term.lam t) (Term.lam t')

/-- Every ordinary β-step is a parallel β-step, so `Par` really is a parallel β-reduction. -/
theorem Beta.toPar {s t : Term} (h : Beta s t) : Par s t := by
  induction h with
  | beta s t => exact Par.beta (Par.refl s) (Par.refl t)
  | appL t _ ih => exact Par.app ih (Par.refl t)
  | appR s _ ih => exact Par.app (Par.refl s) ih
  | lam _ ih => exact Par.lam ih

/-! ### Takahashi's complete development -/

/-- The complete development of a term: contract all β-redexes present simultaneously. -/
def cd : Term → Term
  | var n => var n
  | app (lam s) t => subst1 (cd t) (cd s)
  | app s t => app (cd s) (cd t)
  | lam t => lam (cd t)

@[simp] theorem cd_var (n : Nat) : cd (var n) = var n := rfl
@[simp] theorem cd_lam (t : Term) : cd (lam t) = lam (cd t) := rfl
@[simp] theorem cd_app_lam (s t : Term) : cd (app (lam s) t) = subst1 (cd t) (cd s) := rfl

theorem cd_app_of_not_lam {s : Term} (h : ∀ u, s ≠ lam u) (t : Term) :
    cd (app s t) = app (cd s) (cd t) := by
  cases s with
  | var n => rfl
  | app a b => rfl
  | lam u => exact absurd rfl (h u)

/-- Takahashi's triangle property: every parallel reduct of `s` reduces to `cd s`. -/
theorem Par.triangle {s t : Term} (h : Par s t) : Par t (cd s) := by
  induction h with
  | var n => exact Par.var n
  | @app s s' t t' hs _ ih₁ ih₂ =>
      cases s with
      | var n =>
          rw [cd_app_of_not_lam (by intro u; exact Term.noConfusion)]
          exact Par.app ih₁ ih₂
      | app a b =>
          rw [cd_app_of_not_lam (by intro u; exact Term.noConfusion)]
          exact Par.app ih₁ ih₂
      | lam u =>
          obtain ⟨u', rfl, _⟩ := hs.lam_inv
          rw [cd_app_lam]
          have hu : Par u' (cd u) := by
            have := ih₁
            rw [cd_lam] at this
            obtain ⟨v, hv, hpar⟩ := this.lam_inv
            have hvu : v = cd u := by injection hv.symm
            exact hvu ▸ hpar
          exact Par.beta hu ih₂
  | lam _ ih => exact Par.lam ih
  | beta _ _ ih₁ ih₂ =>
      rw [cd_app_lam]
      exact Par.subst1 ih₁ ih₂

end Term

/-- **Church–Rosser, diamond property for parallel β-reduction.**
If a λ-term `s` reduces in one parallel β-step to both `t₁` and `t₂`, then `t₁` and `t₂`
have a common one-step parallel β-reduct. -/
theorem church_rosser_beta_diamond {s t₁ t₂ : Term}
    (h₁ : Term.Par s t₁) (h₂ : Term.Par s t₂) :
    ∃ u : Term, Term.Par t₁ u ∧ Term.Par t₂ u :=
  ⟨Term.cd s, h₁.triangle, h₂.triangle⟩

end CS

#print axioms CS.church_rosser_beta_diamond

