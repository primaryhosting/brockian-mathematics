/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring, so the header above is a plain comment
-- and is repeated below as the module docstring.)
import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A *friendship graph*: any two distinct vertices have exactly one common neighbour
("every two people have exactly one common friend"). -/

theorem exists_regular_of_no_politician [Nonempty V] (hG : IsFriendshipGraph G)
    (hnp : ¬ ∃ v, IsPolitician G v) : ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  refine ⟨G.degree v, fun x => ?_⟩
  by_cases hvx : G.Adj v x
  swap; · exact (degree_eq_of_not_adj hG hvx).symm
  simp only [IsPolitician, not_exists, not_forall] at hnp
  obtain ⟨w, hwv, hvw⟩ := hnp v
  obtain ⟨y, hyx, hxy⟩ := hnp x
  by_cases hxw : G.Adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  refine degree_eq_of_not_adj hG fun hcontra => ?_
  obtain ⟨a, -, huniq⟩ := hG v w (Ne.symm hwv)
  exact hyx (by rw [huniq y ⟨hvy, hcontra.symm⟩, huniq x ⟨hvx, hxw.symm⟩])

/-- A `d`-regular friendship graph has `d ^ 2 - d + 1` vertices. -/
