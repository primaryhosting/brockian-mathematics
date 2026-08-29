/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (This development is self-contained: it needs nothing beyond Lean 4 core.
--  A module docstring header must precede any `import`, so no imports are used.)

set_option autoImplicit false

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term : Type
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Lift a renaming under a binder. -/
def upren (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => r n + 1

/-- Renaming of free variables. -/
def rename (r : Nat → Nat) : Term → Term
  | .var n => .var (r n)
  | .app s t => .app (rename r s) (rename r t)
  | .lam t => .lam (rename (upren r) t)

/-- Lift a substitution under a binder. -/
def up (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

/-- Parallel substitution. -/
def subst (σ : Nat → Term) : Term → Term
  | .var n => σ n
  | .app s t => .app (subst σ s) (subst σ t)
  | .lam t => .lam (subst (up σ) t)

/-- `cons u σ` is the substitution sending `0` to `u` and `n+1` to `σ n`. -/
def cons (u : Term) (σ : Nat → Term) : Nat → Term
  | 0 => u
  | n + 1 => σ n

/-- Substitution of a single term for the variable `0` (β-substitution). -/
def beta (s u : Term) : Term := subst (cons u Term.var) s

/-! ### Basic substitution calculus -/

theorem upren_comp (r₁ r₂ : Nat → Nat) :
    (fun n => upren r₂ (upren r₁ n)) = upren (fun n => r₂ (r₁ n)) := by
  funext n; cases n <;> rfl

theorem rename_rename (r₁ r₂ : Nat → Nat) (t : Term) :
    rename r₂ (rename r₁ t) = rename (fun n => r₂ (r₁ n)) t := by
  induction t generalizing r₁ r₂ with
  | var n => rfl
  | app s t ihs iht => simp [rename, ihs, iht]
  | lam t ih => simp [rename, ih, upren_comp]

theorem up_upren (σ : Nat → Term) (r : Nat → Nat) :
    (fun n => up σ (upren r n)) = up (fun n => σ (r n)) := by
  funext n; cases n <;> rfl

theorem subst_rename (σ : Nat → Term) (r : Nat → Nat) (t : Term) :
    subst σ (rename r t) = subst (fun n => σ (r n)) t := by
  induction t generalizing σ r with
  | var n => rfl
  | app s t ihs iht => simp [rename, subst, ihs, iht]
  | lam t ih => simp [rename, subst, ih, up_upren]

theorem rename_up (σ : Nat → Term) (r : Nat → Nat) :
    (fun n => rename (upren r) (up σ n)) = up (fun n => rename r (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show rename (upren r) (rename Nat.succ (σ n)) = rename Nat.succ (rename r (σ n))
      rw [rename_rename, rename_rename]
      rfl

theorem rename_subst (σ : Nat → Term) (r : Nat → Nat) (t : Term) :
    rename r (subst σ t) = subst (fun n => rename r (σ n)) t := by
  induction t generalizing σ r with
  | var n => rfl
  | app s t ihs iht => simp [rename, subst, ihs, iht]
  | lam t ih => simp [rename, subst, ih, rename_up]

theorem up_comp (σ τ : Nat → Term) :
    (fun n => subst (up τ) (up σ n)) = up (fun n => subst τ (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show subst (up τ) (rename Nat.succ (σ n)) = rename Nat.succ (subst τ (σ n))
      rw [subst_rename, rename_subst]
      rfl

theorem subst_subst (σ τ : Nat → Term) (t : Term) :
    subst τ (subst σ t) = subst (fun n => subst τ (σ n)) t := by
  induction t generalizing σ τ with
  | var n => rfl
  | app s t ihs iht => simp [subst, ihs, iht]
  | lam t ih => simp [subst, ih, up_comp]

theorem up_var : up Term.var = Term.var := by
  funext n; cases n <;> rfl

theorem subst_var (t : Term) : subst Term.var t = t := by
  induction t with
  | var n => rfl
  | app s t ihs iht => simp [subst, ihs, iht]
  | lam t ih => simp [subst, up_var, ih]

theorem rename_beta (r : Nat → Nat) (s t : Term) :
    rename r (beta s t) = beta (rename (upren r) s) (rename r t) := by
  unfold beta
  rw [rename_subst, subst_rename]
  congr 1
  funext n
  cases n <;> rfl

theorem subst_beta (σ : Nat → Term) (s t : Term) :
    subst σ (beta s t) = beta (subst (up σ) s) (subst σ t) := by
  unfold beta
  rw [subst_subst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show subst σ (Term.var n) = subst (cons (subst σ t) Term.var) (rename Nat.succ (σ n))
      rw [subst_rename]
      show σ n = subst Term.var (σ n)
      rw [subst_var]

end Term

/-! ### Parallel one-step β-reduction -/

/-- One-step parallel β-reduction: any set of β-redexes present in a term may be
contracted simultaneously. -/
inductive Par : Term → Term → Prop
  | var (n : Nat) : Par (.var n) (.var n)
  | app {s s' t t' : Term} : Par s s' → Par t t' → Par (.app s t) (.app s' t')
  | lam {t t' : Term} : Par t t' → Par (.lam t) (.lam t')
  | beta {s s' t t' : Term} : Par s s' → Par t t' →
      Par (.app (.lam s) t) (Term.beta s' t')

namespace Par

theorem refl : ∀ t : Term, Par t t
  | .var n => .var n
  | .app s t => .app (refl s) (refl t)
  | .lam t => .lam (refl t)

theorem rename {s t : Term} (h : Par s t) :
    ∀ r : Nat → Nat, Par (Term.rename r s) (Term.rename r t) := by
  induction h with
  | var n => intro r; exact .var _
  | app _ _ ihs iht => intro r; exact .app (ihs r) (iht r)
  | lam _ ih => intro r; exact .lam (ih _)
  | beta _ _ ihs iht =>
      intro r
      rw [Term.rename_beta]
      exact .beta (ihs _) (iht r)

theorem up_par {σ τ : Nat → Term} (h : ∀ n, Par (σ n) (τ n)) :
    ∀ n, Par (Term.up σ n) (Term.up τ n) := by
  intro n
  cases n with
  | zero => exact .var 0
  | succ n => exact (h n).rename Nat.succ

theorem subst {s t : Term} (h : Par s t) :
    ∀ {σ τ : Nat → Term}, (∀ n, Par (σ n) (τ n)) →
      Par (Term.subst σ s) (Term.subst τ t) := by
  induction h with
  | var n => intro σ τ hst; exact hst n
  | app _ _ ihs iht => intro σ τ hst; exact .app (ihs hst) (iht hst)
  | lam _ ih => intro σ τ hst; exact .lam (ih (up_par hst))
  | beta _ _ ihs iht =>
      intro σ τ hst
      rw [Term.subst_beta]
      exact .beta (ihs (up_par hst)) (iht hst)

theorem beta_cong {s s' t t' : Term} (hs : Par s s') (ht : Par t t') :
    Par (Term.beta s t) (Term.beta s' t') := by
  refine hs.subst (fun n => ?_)
  cases n with
  | zero => exact ht
  | succ n => exact .var n

theorem lam_inv {u t : Term} (h : Par (.lam u) t) : ∃ v, t = .lam v ∧ Par u v := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

end Par

/-! ### Ordinary β-reduction, sandwiching `Par`

These lemmas certify that `Par` is a faithful notion of *one-step parallel*
β-reduction: it contains ordinary one-step β-reduction and is contained in its
reflexive-transitive closure. -/

/-- Ordinary one-step β-reduction. -/
inductive Step : Term → Term → Prop
  | beta (s t : Term) : Step (.app (.lam s) t) (Term.beta s t)
  | appL {s s' t : Term} : Step s s' → Step (.app s t) (.app s' t)
  | appR {s t t' : Term} : Step t t' → Step (.app s t) (.app s t')
  | lam {t t' : Term} : Step t t' → Step (.lam t) (.lam t')

/-- Reflexive-transitive closure of one-step β-reduction. -/
inductive Steps : Term → Term → Prop
  | refl (t : Term) : Steps t t
  | tail {s t u : Term} : Steps s t → Step t u → Steps s u

namespace Steps

theorem trans {s t u : Term} (h₁ : Steps s t) (h₂ : Steps t u) : Steps s u := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hst ih => exact .tail ih hst

theorem single {s t : Term} (h : Step s t) : Steps s t := .tail (.refl s) h

theorem appL {s s' t : Term} (h : Steps s s') : Steps (.app s t) (.app s' t) := by
  induction h with
  | refl => exact .refl _
  | tail _ hst ih => exact .tail ih (.appL hst)

theorem appR {s t t' : Term} (h : Steps t t') : Steps (.app s t) (.app s t') := by
  induction h with
  | refl => exact .refl _
  | tail _ hst ih => exact .tail ih (.appR hst)

theorem lam {t t' : Term} (h : Steps t t') : Steps (.lam t) (.lam t') := by
  induction h with
  | refl => exact .refl _
  | tail _ hst ih => exact .tail ih (.lam hst)

end Steps

/-- Ordinary one-step β-reduction is a parallel reduction step. -/
theorem Step.toPar {s t : Term} (h : Step s t) : Par s t := by
  induction h with
  | beta s t => exact .beta (Par.refl s) (Par.refl t)
  | appL _ ih => exact .app ih (Par.refl _)
  | appR _ ih => exact .app (Par.refl _) ih
  | lam _ ih => exact .lam ih

/-- A parallel reduction step is a finite sequence of ordinary β-steps. -/
theorem Par.toSteps {s t : Term} (h : Par s t) : Steps s t := by
  induction h with
  | var n => exact .refl _
  | app _ _ ihs iht => exact (Steps.appL ihs).trans (Steps.appR iht)
  | lam _ ih => exact Steps.lam ih
  | @beta s s' t t' _ _ ihs iht =>
      refine Steps.trans ?_ (Steps.single (Step.beta s' t'))
      exact (Steps.appL (Steps.lam ihs)).trans (Steps.appR iht)

/-! ### Complete development (Takahashi) -/

/-- The complete development of a term: contract *all* β-redexes present. -/
def cd : Term → Term
  | .var n => .var n
  | .lam t => .lam (cd t)
  | .app (.lam u) t => Term.beta (cd u) (cd t)
  | .app s t => .app (cd s) (cd t)

/-- Takahashi's triangle property: every parallel reduct of `s` parallel-reduces to
the complete development of `s`. -/
theorem par_triangle {s t : Term} (h : Par s t) : Par t (cd s) := by
  induction h with
  | var n => exact .var n
  | @app s s' t t' h1 _ ih1 ih2 =>
      cases s with
      | var n => exact .app ih1 ih2
      | app a b => exact .app ih1 ih2
      | lam u =>
          obtain ⟨u', rfl, _⟩ := Par.lam_inv h1
          have hu : Par u' (cd u) := by
            cases ih1 with
            | lam h => exact h
          exact .beta hu ih2
  | lam _ ih => exact .lam ih
  | beta _ _ ih1 ih2 => exact Par.beta_cong ih1 ih2

/-- **Church-Rosser, diamond property for one-step parallel β-reduction.**
If a λ-term `a` parallel-β-reduces in one step to both `b` and `c`, then `b` and `c`
can be joined by one further step of parallel β-reduction. -/
theorem church_rosser_beta_diamond {a b c : Term} (hb : Par a b) (hc : Par a c) :
    ∃ d, Par b d ∧ Par c d :=
  ⟨cd a, par_triangle hb, par_triangle hc⟩

end CS

