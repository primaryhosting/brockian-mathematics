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

theorem reachLe_card_of_reflTransGen {E : V → V → Prop} {u v : V}
    (h : Relation.ReflTransGen E u v) : reachLe E (Fintype.card V) u v := by
  classical
  -- first: `reachLe` holds for some `n`
  have hex : ∃ n, reachLe E n u v := by
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail hab hbc ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, reachLe_succ_of_step hn hbc⟩
  obtain ⟨n, hn⟩ := hex
  set N := Fintype.card V with hN
  by_cases hstab : ∃ m < N, reachSet E u (m + 1) = reachSet E u m
  · obtain ⟨m, hmN, hm⟩ := hstab
    rcases Nat.le_total n m with hnm | hnm
    · exact reachLe_mono (le_trans hnm (le_of_lt hmN)) hn
    · have : v ∈ reachSet E u (m + (n - m)) := by
        have : m + (n - m) = n := by omega
        rw [this]; exact mem_reachSet.2 hn
      rw [reachSet_stable hm] at this
      exact reachLe_mono (le_of_lt hmN) (mem_reachSet.1 this)
  · push_neg at hstab
    have := card_le_card_reachSet (E := E) (u := u) N (fun m hm => hstab m hm)
    have hcard : (reachSet E u N).card ≤ N := by
      simpa [hN] using Finset.card_le_univ (reachSet E u N)
    omega

end Finite

/-! ### The Boolean divide-and-conquer specification -/

section Spec

variable [DecidableEq V]

/-- `sreach E all k u v` decides whether `v` is reachable from `u` in at most
`2 ^ k` steps, by the middle-first recursion. -/
