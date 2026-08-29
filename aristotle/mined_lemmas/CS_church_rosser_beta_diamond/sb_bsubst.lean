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

theorem sb_bsubst (σ : Nat → Trm) (s u : Trm) :
    sb σ (bsubst s u) = bsubst (sb (up σ) s) (sb σ u) := by
  unfold bsubst
  rw [sb_sb, sb_sb]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      show sb σ (Trm.var n) = sb (scons (sb σ u) Trm.var) (rn Nat.succ (σ n))
      rw [sb_rn]
      show σ n = sb (fun n => scons (sb σ u) Trm.var (n + 1)) (σ n)
      rw [show (fun n => scons (sb σ u) Trm.var (n + 1)) = Trm.var from rfl, sb_var]

/-! ### Parallel reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Trm → Trm → Prop
  | var (n : Nat) : Par (.var n) (.var n)
  | app {s s' t t' : Trm} : Par s s' → Par t t' → Par (.app s t) (.app s' t')
  | lam {s s' : Trm} : Par s s' → Par (.lam s) (.lam s')
  | beta {s s' t t' : Trm} : Par s s' → Par t t' → Par (.app (.lam s) t) (bsubst s' t')

