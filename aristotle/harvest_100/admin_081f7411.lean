/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Trm : Type
  | var : Nat → Trm
  | app : Trm → Trm → Trm
  | lam : Trm → Trm
  deriving DecidableEq

namespace Trm

/-- Lifting of a renaming under a binder. -/
def upr (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

/-- Renaming of the free variables of a term. -/
def rn (ξ : Nat → Nat) : Trm → Trm
  | .var n => .var (ξ n)
  | .app s t => .app (rn ξ s) (rn ξ t)
  | .lam s => .lam (rn (upr ξ) s)

/-- Lifting of a substitution under a binder. -/
def up (σ : Nat → Trm) : Nat → Trm
  | 0 => .var 0
  | n + 1 => rn Nat.succ (σ n)

/-- Parallel substitution. -/
def sb (σ : Nat → Trm) : Trm → Trm
  | .var n => σ n
  | .app s t => .app (sb σ s) (sb σ t)
  | .lam s => .lam (sb (up σ) s)

/-- Extension of a substitution with a new term for the variable `0`. -/
def scons (u : Trm) (σ : Nat → Trm) : Nat → Trm
  | 0 => u
  | n + 1 => σ n

/-- Single-variable (β-)substitution: `t.[u]`. -/
def bsubst (t u : Trm) : Trm := sb (scons u Trm.var) t

/-! ### Basic substitution calculus -/

theorem upr_comp (ζ ξ : Nat → Nat) : upr ζ ∘ upr ξ = upr (ζ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem rn_rn (ζ ξ : Nat → Nat) (t : Trm) : rn ζ (rn ξ t) = rn (ζ ∘ ξ) t := by
  induction t generalizing ζ ξ with
  | var n => rfl
  | app s t ihs iht => simp [rn, ihs, iht]
  | lam s ih => simp [rn, ih, upr_comp]

theorem rn_up (ξ : Nat → Nat) (σ : Nat → Trm) :
    (fun n => rn (upr ξ) (up σ n)) = up (fun n => rn ξ (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [up, rn_rn]; rfl

theorem rn_sb (ξ : Nat → Nat) (σ : Nat → Trm) (t : Trm) :
    rn ξ (sb σ t) = sb (fun n => rn ξ (σ n)) t := by
  induction t generalizing ξ σ with
  | var n => rfl
  | app s t ihs iht => simp [sb, rn, ihs, iht]
  | lam s ih => simp [sb, rn, ih, rn_up]

theorem up_upr (σ : Nat → Trm) (ξ : Nat → Nat) : (fun n => up σ (upr ξ n)) = up (fun n => σ (ξ n)) := by
  funext n; cases n <;> rfl

theorem sb_rn (σ : Nat → Trm) (ξ : Nat → Nat) (t : Trm) :
    sb σ (rn ξ t) = sb (fun n => σ (ξ n)) t := by
  induction t generalizing σ ξ with
  | var n => rfl
  | app s t ihs iht => simp [sb, rn, ihs, iht]
  | lam s ih => simp [sb, rn, ih, up_upr]

theorem sb_up (σ τ : Nat → Trm) :
    (fun n => sb (up σ) (up τ n)) = up (fun n => sb σ (τ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show sb (up σ) (rn Nat.succ (τ n)) = rn Nat.succ (sb σ (τ n))
      rw [sb_rn, rn_sb]
      rfl

theorem sb_sb (σ τ : Nat → Trm) (t : Trm) :
    sb σ (sb τ t) = sb (fun n => sb σ (τ n)) t := by
  induction t generalizing σ τ with
  | var n => rfl
  | app s t ihs iht => simp [sb, ihs, iht]
  | lam s ih => simp [sb, ih, sb_up]

theorem sb_var (t : Trm) : sb Trm.var t = t := by
  induction t with
  | var n => rfl
  | app s t ihs iht => simp [sb, ihs, iht]
  | lam s ih =>
      have h : up Trm.var = Trm.var := by funext n; cases n <;> rfl
      simp [sb, h, ih]

/-- Renaming commutes with β-substitution. -/
theorem rn_bsubst (ξ : Nat → Nat) (s u : Trm) :
    rn ξ (bsubst s u) = bsubst (rn (upr ξ) s) (rn ξ u) := by
  unfold bsubst
  rw [rn_sb, sb_rn]
  congr 1
  funext n
  cases n <;> rfl

/-- Substitution composed with β-substitution. -/
theorem sb_bsubst (σ : Nat → Trm) (s u : Trm) :
    sb σ (bsubst s u) = bsubst (sb (up σ) s) (sb σ u) := by
  unfold bsubst
  rw [sb_sb, sb_sb]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show sb σ (Trm.var n) = sb (scons (sb σ u) Trm.var) (rn Nat.succ (σ n))
      rw [sb_rn]
      show σ n = sb (fun n => scons (sb σ u) Trm.var (n + 1)) (σ n)
      rw [show (fun n => scons (sb σ u) Trm.var (n + 1)) = Trm.var from rfl, sb_var]

/-! ### Parallel reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Trm → Trm → Prop
  | var (n : Nat) : Par (.var n) (.var n)
  | app {s s' t t' : Trm} : Par s s' → Par t t' → Par (.app s t) (.app s' t')
  | lam {s s' : Trm} : Par s s' → Par (.lam s) (.lam s')
  | beta {s s' t t' : Trm} : Par s s' → Par t t' → Par (.app (.lam s) t) (bsubst s' t')

theorem Par.refl (t : Trm) : Par t t := by
  induction t with
  | var n => exact .var n
  | app s t ihs iht => exact .app ihs iht
  | lam s ih => exact .lam ih

theorem Par.rn {s t : Trm} (h : Par s t) (ξ : Nat → Nat) : Par (Trm.rn ξ s) (Trm.rn ξ t) := by
  induction h generalizing ξ with
  | var n => exact .var _
  | app _ _ ihs iht => exact .app (ihs ξ) (iht ξ)
  | lam _ ih => exact .lam (ih _)
  | beta _ _ ihs iht =>
      rw [Trm.rn_bsubst]
      exact .beta (ihs _) (iht ξ)

theorem Par.up {σ τ : Nat → Trm} (h : ∀ n, Par (σ n) (τ n)) (n : Nat) :
    Par (Trm.up σ n) (Trm.up τ n) := by
  cases n with
  | zero => exact .var 0
  | succ n => exact (h n).rn Nat.succ

theorem Par.sb {s s' : Trm} (h : Par s s') {σ τ : Nat → Trm} (hσ : ∀ n, Par (σ n) (τ n)) :
    Par (Trm.sb σ s) (Trm.sb τ s') := by
  induction h generalizing σ τ with
  | var n => exact hσ n
  | app _ _ ihs iht => exact .app (ihs hσ) (iht hσ)
  | lam _ ih => exact .lam (ih (Par.up hσ))
  | beta _ _ ihs iht =>
      rw [Trm.sb_bsubst]
      exact .beta (ihs (Par.up hσ)) (iht hσ)

theorem Par.bsubst {s s' u u' : Trm} (hs : Par s s') (hu : Par u u') :
    Par (Trm.bsubst s u) (Trm.bsubst s' u') := by
  refine hs.sb (σ := Trm.scons u Trm.var) (τ := Trm.scons u' Trm.var) ?_
  intro n
  cases n with
  | zero => exact hu
  | succ n => exact .var n

/-! ### Complete development (Takahashi) -/

/-- The complete development of a term: contract all β-redexes present in it. -/
def dev : Trm → Trm
  | .var n => .var n
  | .lam s => .lam (dev s)
  | .app (.lam u) t => Trm.bsubst (dev u) (dev t)
  | .app (.var n) t => .app (.var n) (dev t)
  | .app (.app a b) t => .app (dev (.app a b)) (dev t)

theorem dev_lam (s : Trm) : dev (.lam s) = .lam (dev s) := by simp [dev]

theorem dev_app_lam (u t : Trm) : dev (.app (.lam u) t) = Trm.bsubst (dev u) (dev t) := by
  simp [dev]

theorem dev_app_var (n : Nat) (t : Trm) :
    dev (.app (.var n) t) = .app (dev (.var n)) (dev t) := by simp [dev]

theorem dev_app_app (a b t : Trm) :
    dev (.app (.app a b) t) = .app (dev (.app a b)) (dev t) := by simp [dev]

theorem Par.lam_inv {a b : Trm} (h : Par (.lam a) (.lam b)) : Par a b := by
  cases h with
  | lam h => exact h

/-- Takahashi's triangle property. -/
theorem Par.triangle {s t : Trm} (h : Par s t) : Par t (dev s) := by
  induction h with
  | var n => exact .var n
  | @app s s' t t' hs _ ihs iht =>
      cases s with
      | var n => rw [dev_app_var]; exact .app ihs iht
      | app a b => rw [dev_app_app]; exact .app ihs iht
      | lam u =>
          rw [dev_app_lam]
          cases hs with
          | lam hu => exact .beta (Par.lam_inv (dev_lam u ▸ ihs)) iht
  | lam _ ih => rw [dev_lam]; exact .lam ih
  | beta _ _ ihs iht =>
      rw [dev_app_lam]
      exact Par.bsubst ihs iht

end Trm

/-- **The diamond property of one-step parallel β-reduction.** If a λ-term `s` reduces in one
parallel β-step to both `t₁` and `t₂`, then `t₁` and `t₂` reduce in one parallel β-step to a
common term. -/
theorem church_rosser_beta_diamond {s t₁ t₂ : Trm} (h₁ : Trm.Par s t₁) (h₂ : Trm.Par s t₂) :
    ∃ u : Trm, Trm.Par t₁ u ∧ Trm.Par t₂ u :=
  ⟨Trm.dev s, h₁.triangle, h₂.triangle⟩

end CS

#print axioms CS.church_rosser_beta_diamond

import Mathlib
import RequestProject.ChurchRosserBetaDiamond

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

