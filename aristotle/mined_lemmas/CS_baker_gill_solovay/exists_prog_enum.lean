import RequestProject.QueryProg
import RequestProject.Aux

/-!
# An oracle `A` with `P^A = NP^A`

The oracle answers questions about its own relativized nondeterministic
computations.  This is well defined because the query `encodeQ i x t` is *longer*
than any string that can be queried during a computation of cost at most `t` on
input `x`, so the definition can be made by recursion on the length of the query.
-/

namespace CS

open Prog

/-- `AAux n z` is the value of the oracle at `z`, where `n` is the length of `z`;
the recursive calls are only made at strictly shorter strings. -/

theorem exists_prog_enum : ∃ f : ℕ → Prog, Function.Surjective f := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (α := Prog)
  refine ⟨fun n => if hx : ∃ p, g p = n then hx.choose else Prog.done, fun p => ?_⟩
  refine ⟨g p, ?_⟩
  have hx : ∃ q, g q = g p := ⟨p, rfl⟩
  simp only
  rw [dif_pos hx]
  exact hg hx.choose_spec

/-- A fixed enumeration of all programs. -/
