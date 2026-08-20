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

def substOne (t : Term) (s : Term) : Term := subst (cons t Term.var) s

/-- Parallel one-step β-reduction. -/
inductive Par : Term → Term → Prop
  | var (i : Nat) : Par (.var i) (.var i)
  | app {s s' t t' : Term} : Par s s' → Par t t' → Par (.app s t) (.app s' t')
  | lam {s s' : Term} : Par s s' → Par (.lam s) (.lam s')
  | beta {s s' t t' : Term} : Par s s' → Par t t' →
      Par (.app (.lam s) t) (substOne t' s')

