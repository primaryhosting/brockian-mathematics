/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Statement: One-step parallel β-reduction in the λ-calculus has the diamond property.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Lam where
  | var : ℕ → Lam
  | app : Lam → Lam → Lam
  | lam : Lam → Lam
  deriving DecidableEq

namespace Lam

/-- Lifting a renaming under a binder. -/
def upr (xi : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => xi n + 1

/-- Renaming of the free variables of a term. -/
def rename (xi : ℕ → ℕ) : Lam → Lam
  | .var n => .var (xi n)
  | .app a b => .app (rename xi a) (rename xi b)
  | .lam t => .lam (rename (upr xi) t)

/-- Lifting a substitution under a binder. -/
def up (sigma : ℕ → Lam) : ℕ → Lam
  | 0 => .var 0
  | n + 1 => rename Nat.succ (sigma n)

/-- Parallel substitution. -/
def subst (sigma : ℕ → Lam) : Lam → Lam
  | .var n => sigma n
  | .app a b => .app (subst sigma a) (subst sigma b)
  | .lam t => .lam (subst (up sigma) t)

/-- The substitution replacing variable `0` by `s` and decrementing the others. -/
def beta (s : Lam) : ℕ → Lam
  | 0 => s
  | n + 1 => .var n

/-! ### Basic substitution calculus -/

theorem rename_ext {xi zeta : ℕ → ℕ} (h : ∀ n, xi n = zeta n) (t : Lam) :
    rename xi t = rename zeta t := by
  induction t generalizing xi zeta with
  | var n => simp [rename, h]
  | app a b iha ihb => simp [rename, iha h, ihb h]
  | lam t ih =>
      refine congrArg Lam.lam (ih ?_)
      intro n; cases n <;> simp [upr, h]

theorem subst_ext {sigma tau : ℕ → Lam} (h : ∀ n, sigma n = tau n) (t : Lam) :
    subst sigma t = subst tau t := by
  induction t generalizing sigma tau with
  | var n => simp [subst, h]
  | app a b iha ihb => simp [subst, iha h, ihb h]
  | lam t ih =>
      refine congrArg Lam.lam (ih ?_)
      intro n; cases n <;> simp [up, h]

theorem rename_rename (xi zeta : ℕ → ℕ) (t : Lam) :
    rename xi (rename zeta t) = rename (fun n => xi (zeta n)) t := by
  induction t generalizing xi zeta with
  | var n => simp [rename]
  | app a b iha ihb => simp [rename, iha, ihb]
  | lam t ih =>
      refine congrArg Lam.lam ?_
      rw [ih]
      exact rename_ext (by intro n; cases n <;> simp [upr]) t

theorem rename_id (t : Lam) : rename id t = t := by
  induction t with
  | var n => simp [rename]
  | app a b iha ihb => simp [rename, iha, ihb]
  | lam t ih =>
      refine congrArg Lam.lam ?_
      rw [rename_ext (xi := upr id) (zeta := id) (by intro n; cases n <;> simp [upr]) t, ih]

theorem subst_rename (sigma : ℕ → Lam) (xi : ℕ → ℕ) (t : Lam) :
    subst sigma (rename xi t) = subst (fun n => sigma (xi n)) t := by
  induction t generalizing sigma xi with
  | var n => simp [rename, subst]
  | app a b iha ihb => simp [rename, subst, iha, ihb]
  | lam t ih =>
      refine congrArg Lam.lam ?_
      simp only [ih]
      exact subst_ext (by intro n; cases n <;> simp [up, upr]) t

theorem rename_subst (xi : ℕ → ℕ) (sigma : ℕ → Lam) (t : Lam) :
    rename xi (subst sigma t) = subst (fun n => rename xi (sigma n)) t := by
  induction t generalizing sigma xi with
  | var n => simp [subst]
  | app a b iha ihb => simp [rename, subst, iha, ihb]
  | lam t ih =>
      refine congrArg Lam.lam ?_
      simp only [ih]
      refine subst_ext ?_ t
      intro n
      cases n with
      | zero => simp [up, rename, upr]
      | succ n => simp [up, rename_rename, upr]

theorem subst_subst (tau sigma : ℕ → Lam) (t : Lam) :
    subst tau (subst sigma t) = subst (fun n => subst tau (sigma n)) t := by
  induction t generalizing sigma tau with
  | var n => simp [subst]
  | app a b iha ihb => simp [subst, iha, ihb]
  | lam t ih =>
      refine congrArg Lam.lam ?_
      simp only [ih]
      refine subst_ext ?_ t
      intro n
      cases n with
      | zero => simp [up, subst]
      | succ n => simp [up, subst_rename, rename_subst]

theorem subst_id (t : Lam) : subst Lam.var t = t := by
  induction t with
  | var n => simp [subst]
  | app a b iha ihb => simp [subst, iha, ihb]
  | lam t ih =>
      refine congrArg Lam.lam ?_
      rw [subst_ext (sigma := up Lam.var) (tau := Lam.var)
        (by intro n; cases n <;> simp [up, rename]) t, ih]

/-- Renaming commutes with a β-substitution. -/
theorem rename_beta (xi : ℕ → ℕ) (s t : Lam) :
    rename xi (subst (beta s) t) = subst (beta (rename xi s)) (rename (upr xi) t) := by
  rw [rename_subst, subst_rename]
  refine subst_ext ?_ t
  intro n; cases n <;> simp [beta, upr, rename]

/-- Substitution commutes with a β-substitution. -/
theorem subst_beta (sigma : ℕ → Lam) (s t : Lam) :
    subst sigma (subst (beta s) t) = subst (beta (subst sigma s)) (subst (up sigma) t) := by
  rw [subst_subst, subst_subst]
  refine subst_ext ?_ t
  intro n
  cases n with
  | zero => simp [beta, subst, up]
  | succ n =>
      simp only [beta, subst, up, subst_rename]
      exact (subst_id _).symm

/-! ### Parallel β-reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Lam → Lam → Prop
  | var (n : ℕ) : Par (.var n) (.var n)
  | app {a a' b b' : Lam} : Par a a' → Par b b' → Par (.app a b) (.app a' b')
  | lam {t t' : Lam} : Par t t' → Par (.lam t) (.lam t')
  | beta {t t' s s' : Lam} : Par t t' → Par s s' →
      Par (.app (.lam t) s) (subst (beta s') t')

theorem Par.refl (t : Lam) : Par t t := by
  induction t with
  | var n => exact .var n
  | app a b iha ihb => exact .app iha ihb
  | lam t ih => exact .lam ih

theorem Par.rename {t t' : Lam} (h : Par t t') (xi : ℕ → ℕ) :
    Par (Lam.rename xi t) (Lam.rename xi t') := by
  induction h generalizing xi with
  | var n => exact .var _
  | app _ _ iha ihb => exact .app (iha xi) (ihb xi)
  | lam _ ih => exact .lam (ih _)
  | @beta t t' s s' _ _ iht ihs =>
      rw [Lam.rename, Lam.rename, rename_beta]
      exact .beta (iht _) (ihs _)

theorem Par.subst {t t' : Lam} (h : Par t t') {sigma tau : ℕ → Lam}
    (hst : ∀ n, Par (sigma n) (tau n)) :
    Par (Lam.subst sigma t) (Lam.subst tau t') := by
  induction h generalizing sigma tau with
  | var n => simpa [Lam.subst] using hst n
  | app _ _ iha ihb => exact .app (iha hst) (ihb hst)
  | lam _ ih =>
      refine .lam (ih ?_)
      intro n
      cases n with
      | zero => exact .var 0
      | succ n => exact (hst n).rename _
  | @beta t t' s s' _ _ iht ihs =>
      have hup : ∀ n, Par (up sigma n) (up tau n) := by
        intro n
        cases n with
        | zero => exact .var 0
        | succ n => exact (hst n).rename _
      rw [Lam.subst, Lam.subst, subst_beta]
      exact .beta (iht hup) (ihs hst)

/-! ### Complete development (Takahashi) -/

/-- The complete development of a term: contract all β-redexes present. -/
def cd : Lam → Lam
  | .app (.lam t) s => subst (beta (cd s)) (cd t)
  | .app a b => .app (cd a) (cd b)
  | .lam t => .lam (cd t)
  | .var n => .var n

theorem cd_var (n : ℕ) : cd (.var n) = .var n := rfl

theorem cd_lam (t : Lam) : cd (.lam t) = .lam (cd t) := rfl

theorem cd_app_lam (t s : Lam) :
    cd (.app (.lam t) s) = subst (beta (cd s)) (cd t) := rfl

theorem cd_app_var (n : ℕ) (b : Lam) :
    cd (.app (.var n) b) = .app (.var n) (cd b) := rfl

theorem cd_app_app (a₁ a₂ b : Lam) :
    cd (.app (.app a₁ a₂) b) = .app (cd (.app a₁ a₂)) (cd b) := rfl

/-- Takahashi's triangle property. -/
theorem Par.triangle {t u : Lam} (h : Par t u) : Par u (cd t) := by
  induction h with
  | var n => exact .var n
  | lam _ ih => rw [cd_lam]; exact .lam ih
  | @app a a' b b' ha _ iha ihb =>
      cases a with
      | var n =>
          cases ha
          rw [cd_app_var]
          exact .app (.var n) ihb
      | app a₁ a₂ =>
          rw [cd_app_app]
          exact .app iha ihb
      | lam t =>
          rw [cd_app_lam]
          cases ha with
          | lam ht =>
              rw [cd_lam] at iha
              cases iha with
              | lam ih' => exact .beta ih' ihb
  | @beta t t' s s' _ _ iht ihs =>
      rw [cd_app_lam]
      refine Par.subst iht ?_
      intro n
      cases n with
      | zero => exact ihs
      | succ n => exact .var n

end Lam

open Lam in
/-- **Diamond property of parallel β-reduction.**
If a λ-term `t` reduces in one parallel β-step to both `u` and `v`, then `u` and `v`
can be joined by one parallel β-step each. -/
theorem church_rosser_beta_diamond {t u v : Lam} (h₁ : Par t u) (h₂ : Par t v) :
    ∃ w : Lam, Par u w ∧ Par v w :=
  ⟨cd t, h₁.triangle, h₂.triangle⟩

end CS

