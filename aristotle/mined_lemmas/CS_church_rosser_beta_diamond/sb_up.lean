/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Trm : Type
  | var : Nat → Trm
  | app : Trm → Trm → Trm
  | lam : Trm → Trm
  deriving DecidableEq

namespace Trm

/-- Lifting of a renaming under a binder. -/

theorem sb_up (σ τ : Nat → Trm) :
    (fun n => sb (up σ) (up τ n)) = up (fun n => sb σ (τ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show sb (up σ) (rn Nat.succ (τ n)) = rn Nat.succ (sb σ (τ n))
      rw [sb_rn, rn_sb]
      rfl

