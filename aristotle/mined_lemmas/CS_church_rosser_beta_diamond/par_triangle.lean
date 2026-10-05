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
