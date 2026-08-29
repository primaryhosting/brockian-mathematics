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

theorem rename_up (σ : Nat → Term) (r : Nat → Nat) :
    (fun n => rename (upren r) (up σ n)) = up (fun n => rename r (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show rename (upren r) (rename Nat.succ (σ n)) = rename Nat.succ (rename r (σ n))
      rw [rename_rename, rename_rename]
      rfl

