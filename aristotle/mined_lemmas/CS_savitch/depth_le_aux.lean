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

theorem depth_le_aux :
    depth M s x ≤ Nat.clog 2 (Fintype.card M.Q) + Nat.clog 2 (x.length + 1)
      + (s + 1) * Nat.clog 2 (Fintype.card M.Γ) + Nat.clog 2 (s + 1) + 1 := by
  set cQ := Nat.clog 2 (Fintype.card M.Q) with hcQ
  set cn := Nat.clog 2 (x.length + 1) with hcn
  set cG := Nat.clog 2 (Fintype.card M.Γ) with hcG
  set cs := Nat.clog 2 (s + 1) with hcs
  have hQ : Fintype.card M.Q ≤ 2 ^ cQ := Nat.le_pow_clog (by norm_num) _
  have hn : x.length + 1 ≤ 2 ^ cn := Nat.le_pow_clog (by norm_num) _
  have hG : Fintype.card M.Γ ≤ 2 ^ cG := Nat.le_pow_clog (by norm_num) _
  have hs : s + 1 ≤ 2 ^ cs := Nat.le_pow_clog (by norm_num) _
  have hGpow : (Fintype.card M.Γ) ^ (s + 1) ≤ 2 ^ ((s + 1) * cG) := by
    calc (Fintype.card M.Γ) ^ (s + 1) ≤ (2 ^ cG) ^ (s + 1) := Nat.pow_le_pow_left hG _
      _ = 2 ^ (cG * (s + 1)) := by rw [← pow_mul]
      _ = 2 ^ ((s + 1) * cG) := by rw [Nat.mul_comm]
  have hcard : Fintype.card (Conf M x.length s) ≤ 2 ^ (cQ + cn + (s + 1) * cG + cs) := by
    rw [card_conf]
    calc Fintype.card M.Q * ((x.length + 1) * (Fintype.card M.Γ ^ (s + 1) * (s + 1)))
        ≤ 2 ^ cQ * (2 ^ cn * (2 ^ ((s + 1) * cG) * 2 ^ cs)) := by
          exact Nat.mul_le_mul hQ (Nat.mul_le_mul hn (Nat.mul_le_mul hGpow hs))
      _ = 2 ^ (cQ + cn + (s + 1) * cG + cs) := by ring
  have hnum : numNodes M s x ≤ 2 ^ (cQ + cn + (s + 1) * cG + cs + 1) := by
    have hcardN : numNodes M s x = Fintype.card (Conf M x.length s) + 1 := by
      simp [numNodes, Node]
    have hpos : (1 : ℕ) ≤ 2 ^ (cQ + cn + (s + 1) * cG + cs) := Nat.one_le_two_pow
    rw [hcardN, pow_succ]
    omega
  exact Nat.clog_le_of_le_pow hnum

/-- The recursion depth is linear in `s + log |x|`, with a constant depending
only on the machine. -/
