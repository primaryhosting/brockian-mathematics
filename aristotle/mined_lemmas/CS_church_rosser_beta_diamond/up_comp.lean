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

theorem up_comp (σ τ : Nat → Term) :
    (fun n => subst (up τ) (up σ n)) = up (fun n => subst τ (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show subst (up τ) (rename Nat.succ (σ n)) = rename Nat.succ (subst τ (σ n))
      rw [subst_rename, rename_subst]
      rfl

