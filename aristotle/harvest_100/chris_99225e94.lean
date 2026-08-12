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

import Mathlib

set_option autoImplicit false

/-!
# Parallel β-reduction has the diamond property

We formalize the untyped λ-calculus with de Bruijn indices, define parallel
one-step β-reduction `CS.Par`, and prove that it satisfies the diamond
property (Takahashi's method of complete developments).
-/

namespace CS

/-- λ-terms with de Bruijn indices. -/
inductive Term : Type
  | var : ℕ → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

namespace Term

/-- Lifting of a renaming under a binder. -/
def upr (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => r n + 1

/-- Renaming of the free variables of a term. -/
def ren (r : ℕ → ℕ) : Term → Term
  | var n => var (r n)
  | app s t => app (ren r s) (ren r t)
  | lam s => lam (ren (upr r) s)

/-- Lifting of a substitution under a binder. -/
def up (s : ℕ → Term) : ℕ → Term
  | 0 => var 0
  | n + 1 => ren Nat.succ (s n)

/-- Simultaneous substitution. -/
def subst (s : ℕ → Term) : Term → Term
  | var n => s n
  | app t u => app (subst s t) (subst s u)
  | lam t => lam (subst (up s) t)

/-- The substitution sending `0` to `u` and `n+1` to `var n`. -/
def cons (u : Term) : ℕ → Term
  | 0 => u
  | n + 1 => var n

/-- Substitution of a single term for the variable bound by the outermost
binder: this is the term `t[u]` appearing in the β-rule `(λ t) u → t[u]`. -/
def inst (t u : Term) : Term := subst (cons u) t

@[simp] theorem ren_var (r : ℕ → ℕ) (n : ℕ) : ren r (var n) = var (r n) := rfl
@[simp] theorem ren_app (r : ℕ → ℕ) (t u : Term) :
    ren r (app t u) = app (ren r t) (ren r u) := rfl
@[simp] theorem ren_lam (r : ℕ → ℕ) (t : Term) :
    ren r (lam t) = lam (ren (upr r) t) := rfl
@[simp] theorem subst_var (s : ℕ → Term) (n : ℕ) : subst s (var n) = s n := rfl
@[simp] theorem subst_app (s : ℕ → Term) (t u : Term) :
    subst s (app t u) = app (subst s t) (subst s u) := rfl
@[simp] theorem subst_lam (s : ℕ → Term) (t : Term) :
    subst s (lam t) = lam (subst (up s) t) := rfl

theorem upr_comp (r₁ r₂ : ℕ → ℕ) : upr r₂ ∘ upr r₁ = upr (r₂ ∘ r₁) := by
  funext n; cases n <;> rfl

/-- Composition of renamings. -/
theorem ren_ren (r₁ r₂ : ℕ → ℕ) (t : Term) :
    ren r₂ (ren r₁ t) = ren (r₂ ∘ r₁) t := by
  induction t generalizing r₁ r₂ with
  | var n => rfl
  | app t u iht ihu => simp [iht, ihu]
  | lam t ih => simp [ih, upr_comp]

theorem up_comp_upr (s : ℕ → Term) (r : ℕ → ℕ) : up s ∘ upr r = up (s ∘ r) := by
  funext n; cases n <;> rfl

/-- Substituting into a renamed term. -/
theorem subst_ren (s : ℕ → Term) (r : ℕ → ℕ) (t : Term) :
    subst s (ren r t) = subst (s ∘ r) t := by
  induction t generalizing s r with
  | var n => rfl
  | app t u iht ihu => simp [iht, ihu]
  | lam t ih => simp [ih, up_comp_upr]

theorem up_ren_comp (r : ℕ → ℕ) (s : ℕ → Term) :
    up (ren r ∘ s) = ren (upr r) ∘ up s := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    have h : upr r ∘ Nat.succ = Nat.succ ∘ r := by funext m; rfl
    simp [up, Function.comp, ren_ren, h]

/-- Renaming a substituted term. -/
theorem ren_subst (r : ℕ → ℕ) (s : ℕ → Term) (t : Term) :
    ren r (subst s t) = subst (ren r ∘ s) t := by
  induction t generalizing r s with
  | var n => rfl
  | app t u iht ihu => simp [iht, ihu]
  | lam t ih => simp [ih, up_ren_comp]

theorem up_subst_comp (s₁ s₂ : ℕ → Term) :
    up (fun n => subst s₂ (s₁ n)) = fun n => subst (up s₂) (up s₁ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show ren Nat.succ (subst s₂ (s₁ n)) = subst (up s₂) (ren Nat.succ (s₁ n))
    rw [ren_subst, subst_ren]
    rfl

/-- Composition of substitutions. -/
theorem subst_subst (s₁ s₂ : ℕ → Term) (t : Term) :
    subst s₂ (subst s₁ t) = subst (fun n => subst s₂ (s₁ n)) t := by
  induction t generalizing s₁ s₂ with
  | var n => rfl
  | app t u iht ihu => simp [iht, ihu]
  | lam t ih => simp [ih, up_subst_comp]

@[simp] theorem subst_id (t : Term) : subst var t = t := by
  induction t with
  | var n => rfl
  | app t u iht ihu => simp [iht, ihu]
  | lam t ih =>
    have : up var = var := by funext n; cases n <;> rfl
    simp [this, ih]

/-- Renaming commutes with single-variable instantiation. -/
theorem ren_inst (r : ℕ → ℕ) (t u : Term) :
    ren r (inst t u) = inst (ren (upr r) t) (ren r u) := by
  unfold inst
  rw [ren_subst, subst_ren]
  congr 1
  funext n
  cases n <;> rfl

/-- Substitution commutes with single-variable instantiation. -/
theorem subst_inst (s : ℕ → Term) (t u : Term) :
    subst s (inst t u) = inst (subst (up s) t) (subst s u) := by
  unfold inst
  rw [subst_subst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show subst s (var n) = subst (cons (subst s u)) (ren Nat.succ (s n))
    rw [subst_ren]
    show s n = subst (fun m => cons (subst s u) (m + 1)) (s n)
    rw [show (fun m => cons (subst s u) (m + 1)) = var from rfl, subst_id]

end Term

open Term

/-- One-step parallel β-reduction. -/
inductive Par : Term → Term → Prop
  | var (n : ℕ) : Par (var n) (var n)
  | app {t t' u u' : Term} : Par t t' → Par u u' → Par (app t u) (app t' u')
  | lam {t t' : Term} : Par t t' → Par (lam t) (lam t')
  | beta {t t' u u' : Term} : Par t t' → Par u u' → Par (app (lam t) u) (inst t' u')

@[refl] theorem Par.refl (t : Term) : Par t t := by
  induction t with
  | var n => exact Par.var n
  | app t u iht ihu => exact iht.app ihu
  | lam t ih => exact ih.lam

/-- Ordinary single-step β-reduction (β-contraction in an arbitrary context). -/
inductive Beta : Term → Term → Prop
  | beta (t u : Term) : Beta (app (lam t) u) (inst t u)
  | appLeft {t t' : Term} (u : Term) : Beta t t' → Beta (app t u) (app t' u)
  | appRight (t : Term) {u u' : Term} : Beta u u' → Beta (app t u) (app t u')
  | lam {t t' : Term} : Beta t t' → Beta (lam t) (lam t')

/-- A single β-step is in particular a parallel step. -/
theorem Beta.toPar {t u : Term} (h : Beta t u) : Par t u := by
  induction h with
  | beta t u => exact Par.beta (Par.refl t) (Par.refl u)
  | appLeft u _ ih => exact ih.app (Par.refl u)
  | appRight t _ ih => exact (Par.refl t).app ih
  | lam _ ih => exact ih.lam

/-- Parallel reduction is stable under renaming. -/
theorem Par.ren {t t' : Term} (h : Par t t') (r : ℕ → ℕ) :
    Par (Term.ren r t) (Term.ren r t') := by
  induction h generalizing r with
  | var n => exact Par.var _
  | app _ _ iht ihu => exact (iht r).app (ihu r)
  | lam _ ih => exact (ih _).lam
  | beta _ _ iht ihu =>
    rw [ren_inst]
    exact Par.beta (iht _) (ihu r)

theorem Par.up {s s' : ℕ → Term} (h : ∀ n, Par (s n) (s' n)) :
    ∀ n, Par (Term.up s n) (Term.up s' n) := by
  intro n
  cases n with
  | zero => exact Par.var 0
  | succ n => exact (h n).ren Nat.succ

/-- Parallel reduction is stable under (parallel) substitution. -/
theorem Par.subst {s s' : ℕ → Term} (hs : ∀ n, Par (s n) (s' n)) {t t' : Term}
    (h : Par t t') : Par (Term.subst s t) (Term.subst s' t') := by
  induction h generalizing s s' with
  | var n => exact hs n
  | app _ _ iht ihu => exact (iht hs).app (ihu hs)
  | lam _ ih => exact (ih (Par.up hs)).lam
  | beta _ _ iht ihu =>
    rw [subst_inst]
    exact Par.beta (iht (Par.up hs)) (ihu hs)

theorem Par.inst {t t' u u' : Term} (ht : Par t t') (hu : Par u u') :
    Par (Term.inst t u) (Term.inst t' u') := by
  refine Par.subst (s := cons u) (s' := cons u') ?_ ht
  intro n
  cases n with
  | zero => exact hu
  | succ n => exact Par.var n

/-- The complete development of a term: contract all β-redexes present. -/
def star : Term → Term
  | var n => var n
  | lam t => lam (star t)
  | app (lam t) u => inst (star t) (star u)
  | app t u => app (star t) (star u)

@[simp] theorem star_var (n : ℕ) : star (var n) = var n := rfl
@[simp] theorem star_lam (t : Term) : star (lam t) = lam (star t) := rfl
@[simp] theorem star_app_lam (t u : Term) :
    star (app (lam t) u) = inst (star t) (star u) := rfl
@[simp] theorem star_app_var (n : ℕ) (u : Term) :
    star (app (var n) u) = app (var n) (star u) := rfl
@[simp] theorem star_app_app (t₁ t₂ u : Term) :
    star (app (app t₁ t₂) u) = app (star (app t₁ t₂)) (star u) := rfl

/-- Takahashi's triangle property: every parallel reduct of `t` reduces in one
parallel step to the complete development `star t`. -/
theorem Par.triangle {t u : Term} (h : Par t u) : Par u (star t) := by
  induction h with
  | var n => exact Par.var n
  | @app t t' u u' ht hu iht ihu =>
    cases t with
    | var n =>
      cases ht
      simpa using (Par.var n).app ihu
    | app t₁ t₂ => simpa using iht.app ihu
    | lam t₀ =>
      cases ht with
      | lam ht₀ =>
        rename_i t₀'
        rw [star_app_lam]
        cases iht with
        | lam ih => exact Par.beta ih ihu
  | lam _ ih => exact ih.lam
  | beta _ _ iht ihu =>
    rw [star_app_lam]
    exact iht.inst ihu

/-- **Diamond property of parallel β-reduction.** If `t` parallel-reduces in one
step to both `u` and `v`, then `u` and `v` have a common parallel reduct. -/
theorem church_rosser_beta_diamond {t u v : Term} (h₁ : Par t u) (h₂ : Par t v) :
    ∃ w : Term, Par u w ∧ Par v w :=
  ⟨star t, h₁.triangle, h₂.triangle⟩

end CS

