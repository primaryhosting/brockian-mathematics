/-
The configuration graph of a space bounded nondeterministic machine, and the
deterministic middle-first search run on it.
-/
import RequestProject.NTM

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS
namespace Sim

variable (M : NTM) (s : ℕ) (x : List Bool)

/-- Vertices of the configuration graph: the configurations of `M`, plus a sink
`none` which is entered from every accepting configuration. -/
abbrev Node : Type := Option (Conf M x.length s)

/-- Edges of the configuration graph.  A single edge query only inspects the
local transition table of `M` at the scanned symbols. -/

theorem reachLe_add {E : V → V → Prop} (m n : ℕ) (u v : V) :
    reachLe E (m + n) u v ↔ ∃ w, reachLe E m u w ∧ reachLe E n w v := by
  induction n generalizing v with
  | zero =>
      constructor
      · intro h; exact ⟨v, h, rfl⟩
      · rintro ⟨w, hw, rfl⟩; simpa using hw
  | succ n ih =>
      constructor
      · intro h
        rcases h with h | ⟨z, hz, hzv⟩
        · obtain ⟨w, hw1, hw2⟩ := (ih v).1 h
          exact ⟨w, hw1, Or.inl hw2⟩
        · obtain ⟨w, hw1, hw2⟩ := (ih z).1 hz
          exact ⟨w, hw1, Or.inr ⟨z, hw2, hzv⟩⟩
      · rintro ⟨w, hw1, hw2⟩
        rcases hw2 with h | ⟨z, hz, hzv⟩
        · exact Or.inl ((ih v).2 ⟨w, hw1, h⟩)
        · exact Or.inr ⟨z, (ih z).2 ⟨w, hw1, hz⟩, hzv⟩

/-- The halving identity behind Savitch's algorithm. -/
