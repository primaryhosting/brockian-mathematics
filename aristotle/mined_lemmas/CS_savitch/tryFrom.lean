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

def tryFrom (all : List V) (k : ℕ) (u v : V) (i : ℕ) (st : List (Frame V)) : Cfg V :=
  match all[i]? with
  | some m => .call k u m (.mid1 k u v i m :: st)
  | none => .ret false st

/-- One step of the deterministic search machine. -/
