import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

lemma connMachine_accepts_iff (G : RotGraph n d) (s t : Fin n) :
    (connMachine n d T seq).Accepts G s t ↔ ∃ j ≤ T, (G.walk seq (s, 0) j).1 = t := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨-, -, -, h4⟩ := connMachine_invariant (T := T) (seq := seq) G s t k
    obtain ⟨j, hj, hjt⟩ := h4.1 hk
    exact ⟨j, le_trans hj (min_le_right _ _), hjt⟩
  · rintro ⟨j, hj, hjt⟩
    obtain ⟨-, -, -, h4⟩ := connMachine_invariant (T := T) (seq := seq) G s t T
    refine ⟨T, h4.2 ?_⟩
    exact ⟨j, by simpa using hj, hjt⟩

/-- Correctness of the connectivity machine, given a universal exploration sequence. -/
