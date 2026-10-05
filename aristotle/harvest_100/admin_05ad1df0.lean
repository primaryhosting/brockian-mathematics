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
def upr : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | r, (n + 1) => r n + 1

/-- Renaming of free variables. -/
def rename : (Nat → Nat) → Trm → Trm
  | r, var i => var (r i)
  | r, app a b => app (rename r a) (rename r b)
  | r, lam a => lam (rename (upr r) a)

/-- Lifting a substitution under a binder. -/
def up : (Nat → Trm) → Nat → Trm
  | _, 0 => var 0
  | s, (n + 1) => rename Nat.succ (s n)

/-- Parallel (simultaneous) substitution. -/
def subs : (Nat → Trm) → Trm → Trm
  | s, var i => s i
  | s, app a b => app (subs s a) (subs s b)
  | s, lam a => lam (subs (up s) a)

/-- The substitution sending `0` to `b` and `n+1` to `n`. -/
def cons (b : Trm) : Nat → Trm
  | 0 => b
  | (n + 1) => var n

/-- Substitution of `b` for the outermost bound variable of `a`. -/
def sub1 (a b : Trm) : Trm := subs (cons b) a

@[simp] theorem rename_var (r : Nat → Nat) (i : Nat) : rename r (var i) = var (r i) := rfl
@[simp] theorem rename_app (r : Nat → Nat) (a b : Trm) :
    rename r (app a b) = app (rename r a) (rename r b) := rfl
@[simp] theorem rename_lam (r : Nat → Nat) (a : Trm) :
    rename r (lam a) = lam (rename (upr r) a) := rfl
@[simp] theorem subs_var (s : Nat → Trm) (i : Nat) : subs s (var i) = s i := rfl
@[simp] theorem subs_app (s : Nat → Trm) (a b : Trm) :
    subs s (app a b) = app (subs s a) (subs s b) := rfl
@[simp] theorem subs_lam (s : Nat → Trm) (a : Trm) :
    subs s (lam a) = lam (subs (up s) a) := rfl

/-! ### The substitution calculus laws -/

theorem upr_comp (r r' : Nat → Nat) : upr r ∘ upr r' = upr (r ∘ r') := by
  funext n; cases n <;> rfl

theorem rename_rename (t : Trm) (r r' : Nat → Nat) :
    rename r (rename r' t) = rename (r ∘ r') t := by
  induction t generalizing r r' with
  | var i => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, upr_comp]

theorem up_comp_upr (s : Nat → Trm) (r : Nat → Nat) : up s ∘ upr r = up (s ∘ r) := by
  funext n; cases n <;> rfl

theorem subs_rename (t : Trm) (s : Nat → Trm) (r : Nat → Nat) :
    subs s (rename r t) = subs (s ∘ r) t := by
  induction t generalizing s r with
  | var i => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, up_comp_upr]

theorem rename_up (s : Nat → Trm) (r : Nat → Nat) :
    (fun n => rename (upr r) (up s n)) = up (fun n => rename r (s n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [up, rename_rename]; rfl

theorem rename_subs (t : Trm) (s : Nat → Trm) (r : Nat → Nat) :
    rename r (subs s t) = subs (fun n => rename r (s n)) t := by
  induction t generalizing s r with
  | var i => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, rename_up]

theorem subs_id (t : Trm) : subs var t = t := by
  induction t with
  | var i => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih =>
    have h : up var = var := by funext n; cases n <;> rfl
    simp [h, ih]

theorem up_subs (s s' : Nat → Trm) :
    (fun n => subs (up s) (up s' n)) = up (fun n => subs s (s' n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show subs (up s) (rename Nat.succ (s' n)) = rename Nat.succ (subs s (s' n))
    rw [subs_rename, rename_subs]
    rfl

theorem subs_subs (t : Trm) (s s' : Nat → Trm) :
    subs s (subs s' t) = subs (fun n => subs s (s' n)) t := by
  induction t generalizing s s' with
  | var i => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, up_subs]

theorem subs_sub1 (a b : Trm) (s : Nat → Trm) :
    subs s (sub1 a b) = sub1 (subs (up s) a) (subs s b) := by
  unfold sub1
  rw [subs_subs, subs_subs]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show s n = subs (cons (subs s b)) (rename Nat.succ (s n))
    rw [subs_rename]
    exact (subs_id _).symm

theorem rename_eq_subs (t : Trm) (r : Nat → Nat) : rename r t = subs (fun n => var (r n)) t := by
  induction t generalizing r with
  | var i => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih =>
    have h : (fun n => var (upr r n)) = up (fun n => var (r n)) := by
      funext n; cases n <;> rfl
    simp [ih, h]

theorem rename_sub1 (a b : Trm) (r : Nat → Nat) :
    rename r (sub1 a b) = sub1 (rename (upr r) a) (rename r b) := by
  rw [rename_eq_subs, subs_sub1, rename_eq_subs a, rename_eq_subs b]
  congr 2
  funext n; cases n <;> rfl

/-! ### Parallel β-reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Trm → Trm → Prop
  | var (i : Nat) : Par (var i) (var i)
  | lam {a a' : Trm} : Par a a' → Par (lam a) (lam a')
  | app {a a' b b' : Trm} : Par a a' → Par b b' → Par (app a b) (app a' b')
  | beta {a a' b b' : Trm} : Par a a' → Par b b' → Par (app (lam a) b) (sub1 a' b')

theorem Par.refl (t : Trm) : Par t t := by
  induction t with
  | var i => exact Par.var i
  | app a b iha ihb => exact Par.app iha ihb
  | lam a ih => exact Par.lam ih

theorem Par.rename {a a' : Trm} (h : Par a a') (r : Nat → Nat) :
    Par (Trm.rename r a) (Trm.rename r a') := by
  induction h generalizing r with
  | var i => exact Par.var _
  | lam _ ih => exact Par.lam (ih _)
  | app _ _ iha ihb => exact Par.app (iha _) (ihb _)
  | @beta a a' b b' _ _ iha ihb =>
    rw [Trm.rename_sub1]
    exact Par.beta (iha _) (ihb _)

theorem Par.subs {a a' : Trm} (h : Par a a') {s s' : Nat → Trm}
    (hs : ∀ n, Par (s n) (s' n)) : Par (Trm.subs s a) (Trm.subs s' a') := by
  induction h generalizing s s' with
  | var i => exact hs i
  | lam _ ih =>
    refine Par.lam (ih ?_)
    intro n
    cases n with
    | zero => exact Par.var 0
    | succ n => exact (hs n).rename _
  | app _ _ iha ihb => exact Par.app (iha hs) (ihb hs)
  | @beta a a' b b' _ _ iha ihb =>
    rw [Trm.subs_sub1]
    refine Par.beta (iha ?_) (ihb hs)
    intro n
    cases n with
    | zero => exact Par.var 0
    | succ n => exact (hs n).rename _

theorem Par.sub1 {a a' b b' : Trm} (ha : Par a a') (hb : Par b b') :
    Par (Trm.sub1 a b) (Trm.sub1 a' b') := by
  refine ha.subs ?_
  intro n
  cases n with
  | zero => exact hb
  | succ n => exact Par.var n

/-! ### Takahashi's complete development -/

/-- The complete development of a term: contract all β-redexes present. -/
def star : Trm → Trm
  | var i => var i
  | lam a => lam (star a)
  | app (lam a) b => sub1 (star a) (star b)
  | app (var i) b => app (var i) (star b)
  | app (app a₁ a₂) b => app (star (app a₁ a₂)) (star b)

/-- Takahashi's triangle property: every parallel reduct of `t` reduces to `star t`. -/
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

theorem Betas.trans {a b c : Trm} (h₁ : Betas a b) (h₂ : Betas b c) : Betas a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hbc ih => exact ih.tail hbc

theorem Pars.trans {a b c : Trm} (h₁ : Pars a b) (h₂ : Pars b c) : Pars a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hbc ih => exact ih.tail hbc

theorem Beta.par {a b : Trm} (h : Beta a b) : Par a b := by
  induction h with
  | beta a b => exact Par.beta (Par.refl a) (Par.refl b)
  | appL b _ ih => exact Par.app ih (Par.refl b)
  | appR a _ ih => exact Par.app (Par.refl a) ih
  | lam _ ih => exact Par.lam ih

theorem Betas.lam {a a' : Trm} (h : Betas a a') : Betas (Trm.lam a) (Trm.lam a') := by
  induction h with
  | refl => exact Betas.refl _
  | tail _ hbc ih => exact ih.tail hbc.lam

theorem Betas.appL {a a' : Trm} (h : Betas a a') (b : Trm) :
    Betas (Trm.app a b) (Trm.app a' b) := by
  induction h with
  | refl => exact Betas.refl _
  | tail _ hbc ih => exact ih.tail (hbc.appL b)

theorem Betas.appR (a : Trm) {b b' : Trm} (h : Betas b b') :
    Betas (Trm.app a b) (Trm.app a b') := by
  induction h with
  | refl => exact Betas.refl _
  | tail _ hbc ih => exact ih.tail (hbc.appR a)

theorem Par.betas {a b : Trm} (h : Par a b) : Betas a b := by
  induction h with
  | var i => exact Betas.refl _
  | lam _ ih => exact ih.lam
  | app _ _ iha ihb => exact (iha.appL _).trans (Betas.appR _ ihb)
  | @beta a a' b b' _ _ iha ihb =>
    exact ((iha.lam.appL b).trans (Betas.appR _ ihb)).tail (Beta.beta a' b')

theorem Betas.pars {a b : Trm} (h : Betas a b) : Pars a b := by
  induction h with
  | refl => exact Pars.refl _
  | tail _ hbc ih => exact ih.tail hbc.par

theorem Pars.betas {a b : Trm} (h : Pars a b) : Betas a b := by
  induction h with
  | refl => exact Betas.refl _
  | tail _ hbc ih => exact ih.trans hbc.betas

/-- Strip lemma: a single parallel step and a sequence of parallel steps can be joined. -/
theorem par_pars_strip {a b c : Trm} (hab : Par a b) (hac : Pars a c) :
    ∃ d : Trm, Pars b d ∧ Par c d := by
  induction hac with
  | refl => exact ⟨b, Pars.refl b, hab⟩
  | @tail x y _ hxy ih =>
    obtain ⟨d, hbd, hxd⟩ := ih
    exact ⟨star x, hbd.tail (par_star hxd), par_star hxy⟩

/-- Confluence of parallel β-reduction sequences. -/
theorem pars_confluent {a b c : Trm} (hab : Pars a b) (hac : Pars a c) :
    ∃ d : Trm, Pars b d ∧ Pars c d := by
  induction hab with
  | refl => exact ⟨c, hac, Pars.refl c⟩
  | @tail x b _ hxb ih =>
    obtain ⟨d, hxd, hcd⟩ := ih
    obtain ⟨e, hbe, hde⟩ := par_pars_strip hxb hxd
    exact ⟨e, hbe, hcd.trans ((Pars.refl d).tail hde)⟩

/-- **Church-Rosser theorem for β-reduction**: β-reduction is confluent. -/
theorem betas_confluent {a b c : Trm} (hab : Betas a b) (hac : Betas a c) :
    ∃ d : Trm, Betas b d ∧ Betas c d := by
  obtain ⟨d, hbd, hcd⟩ := pars_confluent hab.pars hac.pars
  exact ⟨d, hbd.betas, hcd.betas⟩

end Trm

/-- **Diamond property for parallel β-reduction.**  If a λ-term `t` parallel-β-reduces
in one step to both `u` and `v`, then `u` and `v` have a common parallel-β-reduct. -/
theorem church_rosser_beta_diamond {t u v : Trm} (h₁ : Trm.Par t u) (h₂ : Trm.Par t v) :
    ∃ w : Trm, Trm.Par u w ∧ Trm.Par v w :=
  ⟨Trm.star t, Trm.par_star h₁, Trm.par_star h₂⟩

end CS

