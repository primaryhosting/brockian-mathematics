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

def BrouwerFixedPointProperty : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
      ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

section Basic

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  {g : ι → (∀ i, S i) → ℝ}

