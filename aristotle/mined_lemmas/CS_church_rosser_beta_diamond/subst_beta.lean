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

