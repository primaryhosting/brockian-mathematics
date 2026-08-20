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

theorem exists_maximin [Nonempty M] [Nonempty N] (A : M → N → ℝ) :
    ∃ p ∈ stdSimplex ℝ M, ∃ v : ℝ, (∀ n, v ≤ colPayoff A p n) ∧
      ∀ p' ∈ stdSimplex ℝ M, ∃ n, colPayoff A p' n ≤ v := by
  have hne : (Finset.univ : Finset N).Nonempty := Finset.univ_nonempty
  set F : (M → ℝ) → ℝ :=
    Finset.univ.inf' hne (fun n => fun p : M → ℝ => colPayoff A p n) with hF
  have hFc : Continuous F := Continuous.finset_inf' hne fun n _ => continuous_colPayoff A n
  have hFapply : ∀ p : M → ℝ, F p = Finset.univ.inf' hne fun n => colPayoff A p n := by
    intro p
    rw [hF, Finset.inf'_apply]
  obtain ⟨p, hp, hmax⟩ :=
    (isCompact_stdSimplex M).exists_isMaxOn
      ⟨_, ite_eq_mem_stdSimplex ℝ (Classical.arbitrary M)⟩ hFc.continuousOn
  refine ⟨p, hp, F p, fun n => ?_, fun p' hp' => ?_⟩
  · rw [hFapply p]
    exact Finset.inf'_le _ (Finset.mem_univ n)
  · obtain ⟨n, -, hn⟩ := Finset.exists_mem_eq_inf' hne fun n => colPayoff A p' n
    refine ⟨n, ?_⟩
    have h1 : F p' ≤ F p := hmax hp'
    rw [hFapply p'] at h1
    rw [← hn]
    exact h1

/-- The column player has an optimal (minimax) mixed strategy. -/
