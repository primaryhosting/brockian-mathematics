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

theorem depth_le :
    depth M s x
      ≤ (Nat.clog 2 (Fintype.card M.Q) + Nat.clog 2 (Fintype.card M.Γ) + 3)
        * (s + Nat.clog 2 (x.length + 1) + 1) := by
  set cQ := Nat.clog 2 (Fintype.card M.Q) with hcQ
  set cn := Nat.clog 2 (x.length + 1) with hcn
  set cG := Nat.clog 2 (Fintype.card M.Γ) with hcG
  set T := s + cn + 1 with hT
  have hT1 : 1 ≤ T := by omega
  have h1 : cQ ≤ cQ * T := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : cn ≤ T := by omega
  have h3 : (s + 1) * cG ≤ T * cG := Nat.mul_le_mul_right _ (by omega)
  have h4 : Nat.clog 2 (s + 1) ≤ T := le_trans (clog_le_self _) (by omega)
  have h5 : depth M s x ≤ cQ + cn + (s + 1) * cG + Nat.clog 2 (s + 1) + 1 := depth_le_aux M s x
  calc depth M s x ≤ cQ + cn + (s + 1) * cG + Nat.clog 2 (s + 1) + 1 := h5
    _ ≤ cQ * T + T + T * cG + T + T := by omega
    _ = (cQ + cG + 3) * T := by ring

/-- The width of a frame is at most `5 · depth + 1` bits. -/
