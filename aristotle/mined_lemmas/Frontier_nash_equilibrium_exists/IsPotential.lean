import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to be the very first command in a file, so the header comment
above is placed immediately after it.)
-/

open scoped BigOperators

namespace Frontier

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The pure strategy `a`, viewed as a (degenerate) mixed strategy. -/

def IsPotential (g : ι → (∀ i, S i) → ℝ) (P : (∀ i, S i) → ℝ) : Prop :=
  ∀ (i : ι) (s : ∀ i, S i) (a : S i),
    g i (Function.update s i a) - g i s = P (Function.update s i a) - P s

end Defs

/-- **Brouwer's fixed point theorem**, as a hypothesis: every continuous self-map of a
nonempty compact convex subset of a finite-dimensional real normed space has a fixed
point.  (This form is the standard consequence of Brouwer's theorem for balls; it is not
currently available in Mathlib, so the general existence theorem below is stated as a
Lean-checked reduction to it.) -/
