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

def Dir.move {k : ℕ} : Dir → Fin (k + 1) → Fin (k + 1)
  | .left, p => ⟨p.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.isLt⟩
  | .stay, p => p
  | .right, p => if h : p.val + 1 < k + 1 then ⟨p.val + 1, h⟩ else p

/-- A nondeterministic Turing machine with a read-only input tape (over `Bool`)
and a read/write work tape (over `Γ`). -/
structure NTM where
  /-- The finite set of control states. -/
  Q : Type
  /-- The finite work-tape alphabet. -/
  Γ : Type
  [instQ : Fintype Q]
  [instQd : DecidableEq Q]
  [instG : Fintype Γ]
  [instGd : DecidableEq Γ]
  /-- The blank work-tape symbol. -/
  blank : Γ
  /-- The initial control state. -/
  start : Q
  /-- The accepting control state. -/
  acc : Q
  /-- The transition table: from a state, the symbol scanned on the input tape
  (`none` at the end marker) and the symbol scanned on the work tape, a finite
  list of possible successors (new state, symbol written, input head move,
  work head move). -/
  δ : Q → Option Bool → Γ → List (Q × Γ × Dir × Dir)

attribute [instance] NTM.instQ NTM.instQd NTM.instG NTM.instGd

/-- A configuration of `M` on an input of length `n` running in space `s`:
control state, input head position, work tape contents, work head position. -/
abbrev Conf (M : NTM) (n s : ℕ) : Type :=
  M.Q × Fin (n + 1) × (Fin (s + 1) → M.Γ) × Fin (s + 1)

/-- The initial configuration. -/
