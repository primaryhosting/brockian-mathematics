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

