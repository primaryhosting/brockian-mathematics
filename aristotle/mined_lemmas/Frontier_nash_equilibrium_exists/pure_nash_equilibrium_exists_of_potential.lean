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

theorem pure_nash_equilibrium_exists_of_potential {P : (∀ i, S i) → ℝ} (hP : IsPotential g P) :
    ∃ s, IsPureNashEquilibrium g s := by
  obtain ⟨s, hs⟩ := Finite.exists_max (fun s : (∀ i, S i) => P s)
  refine ⟨s, fun i a => ?_⟩
  have hPle : P (Function.update s i a) ≤ P s := hs (Function.update s i a)
  have := hP i s a
  linarith

/-- **Unconditional case: potential games** have mixed-strategy Nash equilibria (no appeal to
Brouwer's theorem). -/
