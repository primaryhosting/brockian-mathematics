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

set_option grind.warning false

/-!
# The diamond property of parallel β-reduction

We formalise untyped λ-terms in de Bruijn representation, define one-step
*parallel* β-reduction `CS.Par`, and prove that it has the diamond property
(`CS.church_rosser_beta_diamond`), which is the key combinatorial step in the
Church–Rosser theorem.  The proof follows Takahashi: we define the *complete
development* `CS.dev` of a term and show the triangle property
`Par a b → Par b (dev a)`.
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Tm : Type
  | var : ℕ → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  deriving DecidableEq

/-- `shift k t` increments every free variable of `t` with index `≥ k` by one. -/
def shift (k : ℕ) : Tm → Tm
  | .var i => .var (if i < k then i else i + 1)
  | .app a b => .app (shift k a) (shift k b)
  | .lam a => .lam (shift (k + 1) a)

/-- `subst t j s` replaces the variable with index `j` in `t` by `s`, and
decrements the free variables with index `> j`. -/
def subst : Tm → ℕ → Tm → Tm
  | .var i, j, s => if i < j then .var i else if i = j then s else .var (i - 1)
  | .app a b, j, s => .app (subst a j s) (subst b j s)
  | .lam a, j, s => .lam (subst a (j + 1) (shift 0 s))

/-- One-step parallel β-reduction: any set of β-redexes present in a term may be
contracted simultaneously. -/
inductive Par : Tm → Tm → Prop
  | var (i : ℕ) : Par (.var i) (.var i)
  | app {a a' b b' : Tm} : Par a a' → Par b b' → Par (.app a b) (.app a' b')
  | lam {a a' : Tm} : Par a a' → Par (.lam a) (.lam a')
  | beta {a a' b b' : Tm} : Par a a' → Par b b' →
      Par (.app (.lam a) b) (subst a' 0 b')

/-- Takahashi's complete development: contract *all* β-redexes present in a term. -/
def dev : Tm → Tm
  | .var i => .var i
  | .lam a => .lam (dev a)
  | .app (.lam a) b => subst (dev a) 0 (dev b)
  | .app a b => .app (dev a) (dev b)

/-! ### Commutation lemmas for `shift` and `subst` -/

theorem shift_shift (t : Tm) : ∀ (i j : ℕ), i ≤ j →
    shift (j + 1) (shift i t) = shift i (shift j t) := by
  induction t with
  | var n => intro i j hij; simp only [shift, Tm.var.injEq]; split_ifs <;> omega
  | app a b iha ihb => intro i j hij; simp only [shift, iha i j hij, ihb i j hij]
  | lam a ih =>
      intro i j hij
      simp only [shift]
      exact congrArg Tm.lam (ih (i + 1) (j + 1) (by omega))

/-- Substituting for the variable freshly created by `shift` is the identity. -/
theorem subst_shift_same (t : Tm) : ∀ (i : ℕ) (s : Tm), subst (shift i t) i s = t := by
  induction t with
  | var n =>
      intro i s
      simp only [shift, subst]
      split_ifs <;> first | rfl | (congr 1; omega)
  | app a b iha ihb => intro i s; simp only [shift, subst, iha, ihb]
  | lam a ih => intro i s; simp only [shift, subst, ih]

/-- Commuting a `shift` with a small cutoff past a substitution. -/
theorem shift_subst_ge (t : Tm) : ∀ (i j : ℕ) (s : Tm), i ≤ j →
    shift i (subst t j s) = subst (shift i t) (j + 1) (shift i s) := by
  induction t with
  | var n =>
      intro i j s hij
      simp only [shift, subst]
      split_ifs <;>
        first | rfl | (simp only [shift]; split_ifs <;> first | rfl | (congr 1; omega))
              | omega
  | app a b iha ihb =>
      intro i j s hij; simp only [shift, subst, iha i j s hij, ihb i j s hij]
  | lam a ih =>
      intro i j s hij
      simp only [shift, subst]
      rw [ih (i + 1) (j + 1) (shift 0 s) (by omega), shift_shift s 0 i (Nat.zero_le i)]

/-- Commuting a `shift` with a large cutoff past a substitution. -/
theorem shift_subst_le (t : Tm) : ∀ (i j : ℕ) (s : Tm), j ≤ i →
    shift i (subst t j s) = subst (shift (i + 1) t) j (shift i s) := by
  induction t with
  | var n =>
      intro i j s hij
      simp only [shift, subst]
      split_ifs <;>
        first | rfl | (simp only [shift]; split_ifs <;> first | rfl | (congr 1; omega))
              | omega
  | app a b iha ihb =>
      intro i j s hij; simp only [shift, subst, iha i j s hij, ihb i j s hij]
  | lam a ih =>
      intro i j s hij
      simp only [shift, subst]
      rw [ih (i + 1) (j + 1) (shift 0 s) (by omega), shift_shift s 0 i (Nat.zero_le i)]

/-- The de Bruijn substitution lemma. -/
theorem subst_subst (t : Tm) : ∀ (i j : ℕ) (b c : Tm), i ≤ j →
    subst (subst t i b) j c = subst (subst t (j + 1) (shift i c)) i (subst b j c) := by
  induction t with
  | var n =>
      intro i j b c hij
      simp only [subst]
      split_ifs <;>
        first | (exfalso; omega) | rfl
              | (simp only [subst, subst_shift_same]; split_ifs <;>
                  first | (exfalso; omega) | rfl)
  | app x y ihx ihy =>
      intro i j b c hij
      simp only [subst, ihx i j b c hij, ihy i j b c hij]
  | lam x ih =>
      intro i j b c hij
      simp only [subst]
      rw [ih (i + 1) (j + 1) (shift 0 b) (shift 0 c) (by omega),
        shift_shift c 0 i (Nat.zero_le i),
        shift_subst_ge b 0 j c (Nat.zero_le j)]

/-! ### Parallel reduction is compatible with `shift` and `subst` -/

theorem Par.refl (t : Tm) : Par t t := by
  induction t with
  | var n => exact Par.var n
  | app a b iha ihb => exact iha.app ihb
  | lam a ih => exact ih.lam

/-- Inversion for parallel reduction out of an abstraction. -/
theorem Par.lam_inv {a c : Tm} (h : Par (.lam a) c) : ∃ c', c = .lam c' ∧ Par a c' := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

theorem Par.shift {a a' : Tm} (h : Par a a') : ∀ k : ℕ, Par (CS.shift k a) (CS.shift k a') := by
  induction h with
  | var i => intro k; exact Par.refl _
  | app _ _ iha ihb => intro k; exact (iha k).app (ihb k)
  | lam _ ih => intro k; exact (ih (k + 1)).lam
  | @beta p p' q q' _ _ ihp ihq =>
      intro k
      have h := Par.beta (ihp (k + 1)) (ihq k)
      rw [shift_subst_le p' k 0 q' (Nat.zero_le k)]
      exact h

theorem Par.subst {a a' : Tm} (h : Par a a') :
    ∀ (j : ℕ) {b b' : Tm}, Par b b' → Par (CS.subst a j b) (CS.subst a' j b') := by
  induction h with
  | var i =>
      intro j b b' hb
      simp only [CS.subst]
      split_ifs
      · exact Par.refl _
      · exact hb
      · exact Par.refl _
  | app _ _ iha ihb => intro j b b' hb; exact (iha j hb).app (ihb j hb)
  | lam _ ih => intro j b b' hb; exact (ih (j + 1) (hb.shift 0)).lam
  | @beta p p' q q' _ _ ihp ihq =>
      intro j b b' hb
      have h := Par.beta (ihp (j + 1) (hb.shift 0)) (ihq j hb)
      rw [CS.subst, subst_subst p' 0 j q' b' (Nat.zero_le j)]
      exact h

/-! ### Takahashi's triangle property -/

/-- Every parallel reduct of `a` reduces in one parallel step to the complete
development `dev a` of `a`. -/
theorem Par.triangle {a b : Tm} (h : Par a b) : Par b (dev a) := by
  induction h with
  | var i => exact Par.refl _
  | @app x x' y y' hx _ ihx ihy =>
      cases x with
      | var i => exact ihx.app ihy
      | app u v => exact ihx.app ihy
      | lam u =>
          obtain ⟨x'', rfl, -⟩ := hx.lam_inv
          simp only [dev] at ihx ⊢
          obtain ⟨w, hw, hpw⟩ := ihx.lam_inv
          cases hw
          exact Par.beta hpw ihy
  | lam _ ih => exact ih.lam
  | beta _ _ ihp ihq =>
      simp only [dev]
      exact ihp.subst 0 ihq

/-- **Diamond property of one-step parallel β-reduction.**  If a λ-term `a`
reduces in one parallel β-step to both `b` and `c`, then `b` and `c` have a
common parallel β-reduct (namely the complete development of `a`). -/
theorem church_rosser_beta_diamond {a b c : Tm} (hb : Par a b) (hc : Par a c) :
    ∃ d, Par b d ∧ Par c d :=
  ⟨dev a, hb.triangle, hc.triangle⟩

/-- Confluence of the reflexive–transitive closure of parallel β-reduction, an
immediate consequence of the diamond property. -/
theorem par_reflTransGen_confluent {a b c : Tm}
    (hb : Relation.ReflTransGen Par a b) (hc : Relation.ReflTransGen Par a c) :
    ∃ d, Relation.ReflTransGen Par b d ∧ Relation.ReflTransGen Par c d := by
  obtain ⟨d, h1, h2⟩ :=
    Relation.church_rosser
      (fun _ _ _ h1 h2 => by
        obtain ⟨d, hd1, hd2⟩ := church_rosser_beta_diamond h1 h2
        exact ⟨d, Relation.ReflGen.single hd1, Relation.ReflTransGen.single hd2⟩)
      hb hc
  exact ⟨d, h1, h2⟩

/-! ### Church–Rosser for ordinary β-reduction -/

/-- Ordinary one-step β-reduction: contract a single β-redex anywhere in a term. -/
inductive Beta : Tm → Tm → Prop
  | beta (a b : Tm) : Beta (.app (.lam a) b) (subst a 0 b)
  | appL {a a' : Tm} (b : Tm) : Beta a a' → Beta (.app a b) (.app a' b)
  | appR (a : Tm) {b b' : Tm} : Beta b b' → Beta (.app a b) (.app a b')
  | lam {a a' : Tm} : Beta a a' → Beta (.lam a) (.lam a')

/-- Multi-step β-reduction. -/
abbrev Betas : Tm → Tm → Prop := Relation.ReflTransGen Beta

theorem Betas.lam {a a' : Tm} (h : Betas a a') : Betas (.lam a) (.lam a') :=
  Relation.ReflTransGen.lift Tm.lam (fun _ _ => Beta.lam) h

theorem Betas.appL {a a' : Tm} (b : Tm) (h : Betas a a') : Betas (.app a b) (.app a' b) :=
  Relation.ReflTransGen.lift (fun x => Tm.app x b) (fun _ _ hx => Beta.appL b hx) h

theorem Betas.appR (a : Tm) {b b' : Tm} (h : Betas b b') : Betas (.app a b) (.app a b') :=
  Relation.ReflTransGen.lift (fun x => Tm.app a x) (fun _ _ hx => Beta.appR a hx) h

theorem Betas.app {a a' b b' : Tm} (ha : Betas a a') (hb : Betas b b') :
    Betas (.app a b) (.app a' b') :=
  (Betas.appL b ha).trans (Betas.appR a' hb)

/-- A single β-step is a parallel step. -/
theorem Beta.toPar {a b : Tm} (h : Beta a b) : Par a b := by
  induction h with
  | beta a b => exact Par.beta (Par.refl a) (Par.refl b)
  | appL b _ ih => exact ih.app (Par.refl b)
  | appR a _ ih => exact (Par.refl a).app ih
  | lam _ ih => exact ih.lam

/-- A parallel step is a finite sequence of ordinary β-steps. -/
theorem Par.toBetas {a b : Tm} (h : Par a b) : Betas a b := by
  induction h with
  | var i => exact Relation.ReflTransGen.refl
  | app _ _ iha ihb => exact iha.app ihb
  | lam _ ih => exact ih.lam
  | @beta p p' q q' _ _ ihp ihq =>
      exact (Betas.app (Betas.lam ihp) ihq).trans
        (Relation.ReflTransGen.single (Beta.beta p' q'))

/-- **The Church–Rosser theorem.**  Multi-step β-reduction in the untyped
λ-calculus is confluent. -/
theorem church_rosser_beta {a b c : Tm} (hb : Betas a b) (hc : Betas a c) :
    ∃ d, Betas b d ∧ Betas c d := by
  obtain ⟨d, h1, h2⟩ :=
    par_reflTransGen_confluent (a := a) (b := b) (c := c)
      (hb.mono fun _ _ h => h.toPar) (hc.mono fun _ _ h => h.toPar)
  refine ⟨d, ?_, ?_⟩
  · exact Relation.ReflTransGen.trans_induction_on h1
      (fun _ => Relation.ReflTransGen.refl) (fun h => h.toBetas) (fun _ _ h h' => h.trans h')
  · exact Relation.ReflTransGen.trans_induction_on h2
      (fun _ => Relation.ReflTransGen.refl) (fun h => h.toBetas) (fun _ _ h h' => h.trans h')

end CS

