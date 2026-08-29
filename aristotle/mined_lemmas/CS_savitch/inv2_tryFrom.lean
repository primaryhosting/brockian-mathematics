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

theorem inv2_tryFrom {all : List V} {K k : ℕ} {u v : V} {st : List (Frame V)} (i : ℕ)
    (hk : k < K) (hst : ∀ f ∈ st, f.level < K ∧ f.idx < all.length) :
    Inv2 K all (tryFrom all k u v i st) := by
  unfold Inv2 tryFrom
  by_cases hlt : i < all.length
  · rw [List.getElem?_eq_getElem hlt]
    intro f hf
    simp only [Cfg.stack_call, List.mem_cons] at hf
    rcases hf with hf | hf
    · subst hf; exact ⟨by simpa using hk, by simpa using hlt⟩
    · exact hst f hf
  · push_neg at hlt
    rw [List.getElem?_eq_none hlt]
    simpa using hst

