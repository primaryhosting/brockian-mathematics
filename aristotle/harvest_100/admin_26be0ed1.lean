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

theorem Betas.appl {a a' : Tm} (h : Betas a a') (b : Tm) : Betas (app a b) (app a' b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Beta.appl hstep)

theorem Betas.appr (a : Tm) {b b' : Tm} (h : Betas b b') : Betas (app a b) (app a b') := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Beta.appr hstep)

theorem Betas.lam {a a' : Tm} (h : Betas a a') : Betas (lam a) (lam a') := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Beta.lam hstep)

/-- A single β-step is a parallel step. -/
theorem Beta.toPar {a b : Tm} (h : Beta a b) : Par a b := by
  induction h with
  | beta a b => exact .beta (Par.refl a) (Par.refl b)
  | appl _ ih => exact .app ih (Par.refl _)
  | appr _ ih => exact .app (Par.refl _) ih
  | lam _ ih => exact .lam ih

/-- A parallel step is a sequence of β-steps. -/
theorem Par.toBetas {a b : Tm} (h : Par a b) : Betas a b := by
  induction h with
  | var k => exact .refl
  | lam _ ih => exact ih.lam
  | app _ _ iha ihb => exact (iha.appl _).trans (Betas.appr _ ihb)
  | @beta p p' q q' _ _ ihp ihq =>
      exact (((ihp.lam).appl _).trans (Betas.appr _ ihq)).tail (Beta.beta p' q')

theorem betas_of_par_star {a b : Tm} (h : ReflTransGen Par a b) : Betas a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans hstep.toBetas

/-- **Church–Rosser theorem for β-reduction.** If `a` β-reduces in many steps to both `b`
and `c`, then `b` and `c` β-reduce in many steps to a common term. -/
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
def lift (i : Nat) : Tm → Tm
  | var k => if k < i then var k else var (k + 1)
  | app a b => app (lift i a) (lift i b)
  | lam a => lam (lift (i + 1) a)

/-- `subst t n u` replaces the variable with de Bruijn index `n` in `t` by `u`,
decrementing the free variables above `n`. -/
def subst : Tm → Nat → Tm → Tm
  | var k, n, u => if k < n then var k else if k = n then u else var (k - 1)
  | app a b, n, u => app (subst a n u) (subst b n u)
  | lam a, n, u => lam (subst a (n + 1) (lift 0 u))

/-- Auxiliary tactic discharging the variable cases of the lifting/substitution lemmas by
exhaustive case analysis on the index comparisons. -/
local macro "var_case" : tactic => `(tactic|
  (iterate 8 (all_goals (try simp only [lift, subst]); all_goals (try split))
   all_goals (try simp_all)
   all_goals omega))

theorem lift_lift (t : Tm) : ∀ i j, i ≤ j → lift (j + 1) (lift i t) = lift i (lift j t) := by
  induction t with
  | var k => intro i j h; var_case
  | app a b iha ihb => intro i j h; simp [lift, iha i j h, ihb i j h]
  | lam a ih => intro i j h; simp [lift, ih (i + 1) (j + 1) (by omega)]

@[simp] theorem subst_lift (t : Tm) : ∀ i u, subst (lift i t) i u = t := by
  induction t with
  | var k => intro i u; var_case
  | app a b iha ihb => intro i u; simp [lift, subst, iha, ihb]
  | lam a ih => intro i u; simp [lift, subst, ih]

theorem lift_subst_le (t : Tm) :
    ∀ i n u, i ≤ n → lift i (subst t n u) = subst (lift i t) (n + 1) (lift i u) := by
  induction t with
  | var k => intro i n u h; var_case
  | app a b iha ihb => intro i n u h; simp [lift, subst, iha i n u h, ihb i n u h]
  | lam a ih =>
      intro i n u h
      simp [lift, subst, ih (i + 1) (n + 1) (lift 0 u) (by omega),
        lift_lift u 0 i (Nat.zero_le i)]

theorem lift_subst_ge (t : Tm) :
    ∀ i n u, n ≤ i → lift i (subst t n u) = subst (lift (i + 1) t) n (lift i u) := by
  induction t with
  | var k => intro i n u h; var_case
  | app a b iha ihb => intro i n u h; simp [lift, subst, iha i n u h, ihb i n u h]
  | lam a ih =>
      intro i n u h
      simp [lift, subst, ih (i + 1) (n + 1) (lift 0 u) (by omega),
        lift_lift u 0 i (Nat.zero_le i)]

/-- The substitution lemma. -/
theorem subst_subst (t : Tm) : ∀ q b m n, m ≤ n →
    subst (subst t m q) n b = subst (subst t (n + 1) (lift m b)) m (subst q n b) := by
  induction t with
  | var k => intro q b m n h; var_case
  | app a b iha ihb => intro q c m n h; simp [subst, iha q c m n h, ihb q c m n h]
  | lam a ih =>
      intro q b m n h
      simp [subst, ih (lift 0 q) (lift 0 b) (m + 1) (n + 1) (by omega),
        lift_lift b 0 m (Nat.zero_le m), lift_subst_le q 0 n b (Nat.zero_le n)]

/-- One-step parallel β-reduction: any number of β-redexes already present in a term may be
contracted simultaneously, but no redexes created by the contraction. -/
inductive Par : Tm → Tm → Prop
  | var (k : Nat) : Par (var k) (var k)
  | lam {a a' : Tm} : Par a a' → Par (lam a) (lam a')
  | app {a a' b b' : Tm} : Par a a' → Par b b' → Par (app a b) (app a' b')
  | beta {a a' b b' : Tm} : Par a a' → Par b b' → Par (app (lam a) b) (subst a' 0 b')

theorem Par.refl : ∀ t : Tm, Par t t
  | Tm.var k => .var k
  | Tm.app a b => .app (Par.refl a) (Par.refl b)
  | Tm.lam a => .lam (Par.refl a)

theorem Par.lift_par {a b : Tm} (h : Par a b) : ∀ i, Par (Tm.lift i a) (Tm.lift i b) := by
  induction h with
  | var k => intro i; simp only [Tm.lift]; split <;> exact .var _
  | lam _ ih => intro i; exact .lam (ih (i + 1))
  | app _ _ iha ihb => intro i; exact .app (iha i) (ihb i)
  | @beta a a' b b' _ _ iha ihb =>
      intro i
      simp only [Tm.lift, lift_subst_ge a' i 0 b' (Nat.zero_le i)]
      exact .beta (iha (i + 1)) (ihb i)

theorem Par.subst_par {a a' : Tm} (ha : Par a a') :
    ∀ {b b' : Tm}, Par b b' → ∀ n, Par (Tm.subst a n b) (Tm.subst a' n b') := by
  induction ha with
  | var k =>
      intro b b' hb n
      simp only [Tm.subst]
      split
      · exact .var _
      · split
        · exact hb
        · exact .var _
  | lam _ ih => intro b b' hb n; exact .lam (ih (hb.lift_par 0) (n + 1))
  | app _ _ iha ihb => intro b b' hb n; exact .app (iha hb n) (ihb hb n)
  | @beta p p' q q' _ _ ihp ihq =>
      intro b b' hb n
      simp only [Tm.subst, subst_subst p' q' b' 0 n (Nat.zero_le n)]
      exact .beta (ihp (hb.lift_par 0) (n + 1)) (ihq hb n)

/-- The complete development of a term: contract all β-redexes present in it. -/
def cd : Tm → Tm
  | var k => var k
  | lam a => lam (cd a)
  | app (lam a) b => subst (cd a) 0 (cd b)
  | app a b => app (cd a) (cd b)

theorem Par.lam_inv {a s : Tm} (h : Par (Tm.lam a) s) : ∃ a', s = Tm.lam a' ∧ Par a a' := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

/-- Takahashi's triangle property: every parallel reduct of `t` parallel-reduces to the
complete development of `t`. -/
theorem Par.triangle {t s : Tm} (h : Par t s) : Par s (cd t) := by
  induction h with
  | var k => exact .var k
  | lam _ ih => exact .lam ih
  | @app a a' b b' hA _ iha ihb =>
      cases a with
      | var k => simpa [cd] using Par.app iha ihb
      | app p q => simpa [cd] using Par.app iha ihb
      | lam p =>
          obtain ⟨p', rfl, _⟩ := hA.lam_inv
          obtain ⟨r, hr, hr'⟩ := iha.lam_inv
          simp only [cd, Tm.lam.injEq] at hr
          cases hr
          simpa [cd] using Par.beta hr' ihb
  | @beta p p' q q' _ _ ihp ihq => simpa [cd] using ihp.subst_par ihq 0

end Tm

/-- **Diamond property for one-step parallel β-reduction.**
If a λ-term `t` parallel-reduces in one step to both `u` and `v`, then `u` and `v` have a
common one-step parallel reduct (namely the complete development of `t`). -/
theorem church_rosser_beta_diamond {t u v : Tm} (h₁ : Tm.Par t u) (h₂ : Tm.Par t v) :
    ∃ w, Tm.Par u w ∧ Tm.Par v w :=
  ⟨Tm.cd t, h₁.triangle, h₂.triangle⟩

end CS

