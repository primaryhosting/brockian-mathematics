/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term : Type
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

namespace Term

/-- Lift a renaming under a binder. -/

theorem sub_subst1 (s : Nat → Term) (a b : Term) :
    sub s (subst1 a b) = subst1 (sub (up s) a) (sub s b) := by
  unfold subst1
  rw [sub_sub, sub_sub]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      have h1 : (scons (sub s b) var) ∘ Nat.succ = var := by funext m; rfl
      show s n = sub (scons (sub s b) var) (ren Nat.succ (s n))
      rw [sub_ren, h1, sub_var_id]

/-- One-step parallel β-reduction. -/
inductive Par : Term → Term → Prop
  | var (n : Nat) : Par (var n) (var n)
  | app {a a' b b' : Term} : Par a a' → Par b b' → Par (app a b) (app a' b')
  | lam {a a' : Term} : Par a a' → Par (lam a) (lam a')
  | beta {a a' b b' : Term} : Par a a' → Par b b' → Par (app (lam a) b) (subst1 a' b')

