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

theorem inv_tryFrom {all : List V} {K k : ℕ} {u v : V}
    {st : List (Frame V)} (i : ℕ)
    (hlen : k + st.length + 1 = K) (hchain : StackChain st)
    (hhead : ∀ f ∈ st.head?, f.level = k + 1) :
    Inv K (tryFrom all k u v i st) := by
  unfold tryFrom
  rcases hgi : all[i]? with _ | m
  · refine ⟨by omega, hchain, ?_⟩
    intro f hf
    have := hhead f hf
    omega
  · refine ⟨by simp; omega, ⟨?_, hchain⟩, by simp⟩
    intro g hg
    simpa using hhead g hg

