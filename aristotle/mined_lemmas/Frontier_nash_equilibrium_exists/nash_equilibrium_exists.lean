/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/

theorem nash_equilibrium_exists [∀ i, Nonempty (S i)]
    (hB : BrouwerProperty) (G : FiniteGame ι S) :
    ∃ x : (i : ι) → S i → ℝ, IsNash G x := by
  set K : Set ((i : ι) → S i → ℝ) := Set.univ.pi fun i => stdSimplex ℝ (S i) with hK
  have hmem : ∀ x : (i : ι) → S i → ℝ, x ∈ K ↔ IsMixed x := by
    intro x
    simp [hK, IsMixed]
  have hne : K.Nonempty := by
    refine ⟨fun i => pureVec (Classical.arbitrary (S i)), ?_⟩
    rw [hmem]
    intro i
    exact pureVec_mem_stdSimplex _
  have hcomp : IsCompact K := isCompact_univ_pi fun i => isCompact_stdSimplex (S i)
  have hconv : Convex ℝ K := convex_pi fun i _ => convex_stdSimplex ℝ (S i)
  obtain ⟨x, hxK, hfix⟩ := hB _ K hne hcomp hconv (nashMap G) (continuous_nashMap G)
    (fun y hy => (hmem _).2 (nashMap_mapsTo G ((hmem y).1 hy)))
  exact ⟨x, isNash_of_nashMap_eq G ((hmem x).1 hxK) hfix⟩

/-! ### Unconditional cases -/

/-- A pure strategy profile is a pure Nash equilibrium if no player can improve by
switching to another pure strategy. -/
