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

theorem up_par {σ τ : Nat → Term} (h : ∀ n, Par (σ n) (τ n)) :
    ∀ n, Par (Term.up σ n) (Term.up τ n) := by
  intro n
  cases n with
  | zero => exact .var 0
  | succ n => exact (h n).rename Nat.succ

