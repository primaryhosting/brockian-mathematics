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

theorem exists_minimax [Nonempty M] [Nonempty N] (A : M → N → ℝ) :
    ∃ q ∈ stdSimplex ℝ N, ∃ w : ℝ, (∀ m, rowPayoff A q m ≤ w) ∧
      ∀ q' ∈ stdSimplex ℝ N, ∃ m, w ≤ rowPayoff A q' m := by
  have hne : (Finset.univ : Finset M).Nonempty := Finset.univ_nonempty
  set G : (N → ℝ) → ℝ :=
    Finset.univ.sup' hne (fun m => fun q : N → ℝ => rowPayoff A q m) with hG
  have hGc : Continuous G := Continuous.finset_sup' hne fun m _ => continuous_rowPayoff A m
  have hGapply : ∀ q : N → ℝ, G q = Finset.univ.sup' hne fun m => rowPayoff A q m := by
    intro q
    rw [hG, Finset.sup'_apply]
  obtain ⟨q, hq, hmin⟩ :=
    (isCompact_stdSimplex N).exists_isMinOn
      ⟨_, ite_eq_mem_stdSimplex ℝ (Classical.arbitrary N)⟩ hGc.continuousOn
  refine ⟨q, hq, G q, fun m => ?_, fun q' hq' => ?_⟩
  · rw [hGapply q]
    exact Finset.le_sup' _ (Finset.mem_univ m)
  · obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup' hne fun m => rowPayoff A q' m
    refine ⟨m, ?_⟩
    have h1 : G q ≤ G q' := hmin hq'
    rw [hGapply q'] at h1
    rw [← hm]
    exact h1

/-- **von Neumann's minimax theorem**: every finite two-player zero-sum game has a saddle point
in mixed strategies. Unconditional: no fixed point theorem is used. -/
