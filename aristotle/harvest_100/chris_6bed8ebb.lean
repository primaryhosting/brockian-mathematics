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
inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term

namespace Term

/-- Lifting of a renaming under a binder. -/
def upr (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => r n + 1

/-- Renaming of free variables. -/
def rename (r : Nat → Nat) : Term → Term
  | .var i => .var (r i)
  | .app s t => .app (rename r s) (rename r t)
  | .lam s => .lam (rename (upr r) s)

/-- Extending a substitution with a new term at index `0`. -/
def cons (t : Term) (σ : Nat → Term) : Nat → Term
  | 0 => t
  | n + 1 => σ n

/-- Lifting of a substitution under a binder. -/
def up (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Simultaneous substitution. -/
def subst (σ : Nat → Term) : Term → Term
  | .var i => σ i
  | .app s t => .app (subst σ s) (subst σ t)
  | .lam s => .lam (subst (up σ) s)

@[simp] theorem upr_zero (r : Nat → Nat) : upr r 0 = 0 := rfl
@[simp] theorem upr_succ (r : Nat → Nat) (n : Nat) : upr r (n + 1) = r n + 1 := rfl
@[simp] theorem up_zero (σ : Nat → Term) : up σ 0 = .var 0 := rfl
@[simp] theorem up_succ (σ : Nat → Term) (n : Nat) : up σ (n + 1) = rename Nat.succ (σ n) := rfl
@[simp] theorem cons_zero (t : Term) (σ : Nat → Term) : cons t σ 0 = t := rfl
@[simp] theorem cons_succ (t : Term) (σ : Nat → Term) (n : Nat) : cons t σ (n + 1) = σ n := rfl
@[simp] theorem cons_comp_succ (t : Term) (σ : Nat → Term) : cons t σ ∘ Nat.succ = σ := rfl

@[simp] theorem rename_var (r : Nat → Nat) (i : Nat) : rename r (.var i) = .var (r i) := rfl
@[simp] theorem rename_app (r : Nat → Nat) (s t : Term) :
    rename r (.app s t) = .app (rename r s) (rename r t) := rfl
@[simp] theorem rename_lam (r : Nat → Nat) (s : Term) :
    rename r (.lam s) = .lam (rename (upr r) s) := rfl

@[simp] theorem subst_var (σ : Nat → Term) (i : Nat) : subst σ (.var i) = σ i := rfl
@[simp] theorem subst_app (σ : Nat → Term) (s t : Term) :
    subst σ (.app s t) = .app (subst σ s) (subst σ t) := rfl
@[simp] theorem subst_lam (σ : Nat → Term) (s : Term) :
    subst σ (.lam s) = .lam (subst (up σ) s) := rfl

theorem upr_id : upr id = id := by
  funext n; cases n <;> rfl

@[simp] theorem rename_id (t : Term) : rename id t = t := by
  induction t with
  | var i => rfl
  | app s t ihs iht => simp [ihs, iht]
  | lam s ihs => simp [upr_id, ihs]

theorem upr_comp (r₁ r₂ : Nat → Nat) : upr r₁ ∘ upr r₂ = upr (r₁ ∘ r₂) := by
  funext n; cases n <;> rfl

theorem rename_rename (r₁ r₂ : Nat → Nat) (t : Term) :
    rename r₁ (rename r₂ t) = rename (r₁ ∘ r₂) t := by
  induction t generalizing r₁ r₂ with
  | var i => rfl
  | app s t ihs iht => simp [ihs, iht]
  | lam s ihs => simp [ihs, upr_comp]

theorem up_comp_upr (σ : Nat → Term) (r : Nat → Nat) : up σ ∘ upr r = up (σ ∘ r) := by
  funext n; cases n <;> rfl

theorem subst_rename (σ : Nat → Term) (r : Nat → Nat) (t : Term) :
    subst σ (rename r t) = subst (σ ∘ r) t := by
  induction t generalizing σ r with
  | var i => rfl
  | app s t ihs iht => simp [ihs, iht]
  | lam s ihs => simp [ihs, up_comp_upr]

theorem up_rename (σ : Nat → Term) (r : Nat → Nat) :
    up (fun n => rename r (σ n)) = fun n => rename (upr r) (up σ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [rename_rename]; rfl

theorem rename_subst (r : Nat → Nat) (σ : Nat → Term) (t : Term) :
    rename r (subst σ t) = subst (fun n => rename r (σ n)) t := by
  induction t generalizing r σ with
  | var i => rfl
  | app s t ihs iht => simp [ihs, iht]
  | lam s ihs => simp [ihs, up_rename]

theorem up_var : up Term.var = Term.var := by
  funext n; cases n <;> rfl

@[simp] theorem subst_id (t : Term) : subst Term.var t = t := by
  induction t with
  | var i => rfl
  | app s t ihs iht => simp [ihs, iht]
  | lam s ihs => simp [up_var, ihs]

theorem up_subst (σ τ : Nat → Term) :
    up (fun n => subst σ (τ n)) = fun n => subst (up σ) (up τ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp [subst_rename, rename_subst]
      rfl

theorem subst_subst (σ τ : Nat → Term) (t : Term) :
    subst σ (subst τ t) = subst (fun n => subst σ (τ n)) t := by
  induction t generalizing σ τ with
  | var i => rfl
  | app s t ihs iht => simp [ihs, iht]
  | lam s ihs => simp [ihs, up_subst]

/-- Substitution of a single term for the variable `0`. -/
def substOne (t : Term) (s : Term) : Term := subst (cons t Term.var) s

/-- Parallel one-step β-reduction. -/
inductive Par : Term → Term → Prop
  | var (i : Nat) : Par (.var i) (.var i)
  | app {s s' t t' : Term} : Par s s' → Par t t' → Par (.app s t) (.app s' t')
  | lam {s s' : Term} : Par s s' → Par (.lam s) (.lam s')
  | beta {s s' t t' : Term} : Par s s' → Par t t' →
      Par (.app (.lam s) t) (substOne t' s')

theorem Par.refl (t : Term) : Par t t := by
  induction t with
  | var i => exact .var i
  | app s t ihs iht => exact .app ihs iht
  | lam s ihs => exact .lam ihs

theorem Par.rename {s t : Term} (h : Par s t) (r : Nat → Nat) :
    Par (Term.rename r s) (Term.rename r t) := by
  induction h generalizing r with
  | var i => exact .var _
  | app _ _ ihs iht => exact .app (ihs r) (iht r)
  | lam _ ih => exact .lam (ih _)
  | @beta s s' t t' _ _ ihs iht =>
      have key : Term.rename r (substOne t' s')
          = substOne (Term.rename r t') (Term.rename (Term.upr r) s') := by
        unfold substOne
        rw [Term.rename_subst, Term.subst_rename]
        congr 1
        funext n
        cases n <;> rfl
      rw [Term.rename_app, Term.rename_lam, key]
      exact .beta (ihs _) (iht r)

theorem Par.subst {s s' : Term} (h : Par s s') {σ τ : Nat → Term}
    (hστ : ∀ n, Par (σ n) (τ n)) : Par (Term.subst σ s) (Term.subst τ s') := by
  induction h generalizing σ τ with
  | var i => exact hστ i
  | app _ _ ihs iht => exact .app (ihs hστ) (iht hστ)
  | lam _ ih =>
      refine .lam (ih ?_)
      intro n
      cases n with
      | zero => exact .var 0
      | succ n => exact (hστ n).rename Nat.succ
  | @beta s s' t t' _ _ ihs iht =>
      have hup : ∀ n, Par (Term.up σ n) (Term.up τ n) := by
        intro n
        cases n with
        | zero => exact .var 0
        | succ n => exact (hστ n).rename Nat.succ
      have key : Term.subst τ (substOne t' s')
          = substOne (Term.subst τ t') (Term.subst (Term.up τ) s') := by
        unfold substOne
        rw [Term.subst_subst, Term.subst_subst]
        congr 1
        funext n
        cases n with
        | zero => rfl
        | succ n =>
            rw [Term.cons_succ, Term.subst_var, Term.up_succ, Term.subst_rename,
              Term.cons_comp_succ, Term.subst_id]
      rw [Term.subst_app, Term.subst_lam, key]
      exact .beta (ihs hup) (iht hστ)

/-- Takahashi's complete development: contract every β-redex present in the term. -/
def dev : Term → Term
  | .var i => .var i
  | .lam s => .lam (dev s)
  | .app (.lam s) t => substOne (dev t) (dev s)
  | .app (.var i) t => .app (.var i) (dev t)
  | .app (.app s₁ s₂) t => .app (dev (.app s₁ s₂)) (dev t)

@[simp] theorem dev_var (i : Nat) : dev (.var i) = .var i := rfl
@[simp] theorem dev_lam (s : Term) : dev (.lam s) = .lam (dev s) := rfl
@[simp] theorem dev_app_lam (s t : Term) :
    dev (.app (.lam s) t) = substOne (dev t) (dev s) := rfl
@[simp] theorem dev_app_var (i : Nat) (t : Term) :
    dev (.app (.var i) t) = .app (.var i) (dev t) := rfl
@[simp] theorem dev_app_app (s₁ s₂ t : Term) :
    dev (.app (.app s₁ s₂) t) = .app (dev (.app s₁ s₂)) (dev t) := rfl

/-- The triangle property: every parallel reduct of `s` reduces to the complete
development of `s`. -/
theorem Par.triangle {s t : Term} (h : Par s t) : Par t (dev s) := by
  induction h with
  | var i => exact .var i
  | @app s s' t t' hs _ ihs iht =>
      cases s with
      | var i => rw [dev_app_var]; exact .app ihs iht
      | app s₁ s₂ => rw [dev_app_app]; exact .app ihs iht
      | lam s₀ =>
          rw [dev_app_lam]
          cases hs with
          | lam h₀ =>
              rw [dev_lam] at ihs
              cases ihs with
              | lam h₁ => exact .beta h₁ iht
  | lam _ ih => exact .lam ih
  | beta _ _ ihs iht =>
      rw [dev_app_lam]
      refine Par.subst (σ := Term.cons _ Term.var) (τ := Term.cons _ Term.var) ihs ?_
      intro n
      cases n with
      | zero => exact iht
      | succ n => exact .var n

/-- Diamond property for parallel β-reduction. -/
theorem Par.diamond {a b c : Term} (hb : Par a b) (hc : Par a c) :
    ∃ d, Par b d ∧ Par c d :=
  ⟨dev a, hb.triangle, hc.triangle⟩

/-- Reflexive-transitive closure of parallel β-reduction (equivalently, of β-reduction). -/
inductive Pars : Term → Term → Prop
  | refl (a : Term) : Pars a a
  | step {a b c : Term} : Par a b → Pars b c → Pars a c

/-- Strip lemma: a single parallel step and a multi-step reduction can be joined. -/
theorem Pars.strip {a b c : Term} (hb : Par a b) (hc : Pars a c) :
    ∃ d, Pars b d ∧ Par c d := by
  induction hc generalizing b with
  | refl a => exact ⟨b, .refl b, hb⟩
  | @step a b₁ c h₁ _ ih =>
      obtain ⟨e, hbe, hb₁e⟩ := hb.diamond h₁
      obtain ⟨d, hed, hcd⟩ := ih hb₁e
      exact ⟨d, .step hbe hed, hcd⟩

/-- Confluence of multi-step parallel β-reduction. -/
theorem Pars.confluent {a b c : Term} (hb : Pars a b) (hc : Pars a c) :
    ∃ d, Pars b d ∧ Pars c d := by
  induction hb generalizing c with
  | refl a => exact ⟨c, hc, .refl c⟩
  | @step a b₁ b h₁ _ ih =>
      obtain ⟨e, hb₁e, hce⟩ := Pars.strip h₁ hc
      obtain ⟨d, hbd, hed⟩ := ih hb₁e
      exact ⟨d, hbd, .step hce hed⟩

end Term

open Term in
/-- **Diamond property for one-step parallel β-reduction in the λ-calculus.**
If a λ-term `a` parallel-reduces in one step to both `b` and `c`, then `b` and `c`
have a common one-step parallel reduct `d`. -/
theorem church_rosser_beta_diamond {a b c : Term} (hb : Par a b) (hc : Par a c) :
    ∃ d, Par b d ∧ Par c d :=
  hb.diamond hc

open Term in
/-- **Church-Rosser theorem**: multi-step (parallel) β-reduction is confluent. -/
theorem church_rosser_beta {a b c : Term} (hb : Pars a b) (hc : Pars a c) :
    ∃ d, Pars b d ∧ Pars c d :=
  hb.confluent hc

end CS

#print axioms CS.church_rosser_beta_diamond
#print axioms CS.church_rosser_beta

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

