import Mathlib

/-!
# Hadwiger Nelson 5
Category: Frontier — Moonshot
Target: Frontier.hadwiger_nelson_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` commands to appear before any other
command, and a module docstring `/-! ... -/` *is* a command.  The requested header
comment is therefore reproduced verbatim immediately after the single `import` line.
-/

namespace Frontier

open Real

/-! ## The unit-distance graph of the Euclidean plane

We model the Euclidean plane as `ℂ`, whose metric `dist z w = ‖z - w‖` is exactly the
Euclidean distance.  `planeGraph` is the unit-distance graph: two points are adjacent
iff they are at distance `1`.  Its chromatic number is the *chromatic number of the
plane*, the subject of the Hadwiger–Nelson problem.
-/

/-- The unit-distance graph on the Euclidean plane (modelled as `ℂ`). -/

theorem colorable_of_forall_finset {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (h : ∀ S : Finset V, ∃ c : V → Fin n, ∀ z ∈ S, ∀ w ∈ S, G.Adj z w → c z ≠ c w) :
    G.Colorable n := by
  classical
  letI : TopologicalSpace (Fin n) := ⊥
  haveI : DiscreteTopology (Fin n) := ⟨rfl⟩
  haveI : CompactSpace (V → Fin n) := Pi.compactSpace
  set T : Finset V → Set (V → Fin n) :=
    fun S => {c | ∀ z ∈ S, ∀ w ∈ S, G.Adj z w → c z ≠ c w} with hT
  have hne : ∀ S, (T S).Nonempty := fun S => h S
  have hpair : ∀ z w : V, IsClosed {c : V → Fin n | G.Adj z w → c z ≠ c w} := by
    intro z w
    by_cases hzw : G.Adj z w
    · have he : {c : V → Fin n | G.Adj z w → c z ≠ c w}
          = (fun c : V → Fin n => (c z, c w)) ⁻¹' {p : Fin n × Fin n | p.1 ≠ p.2} := by
        ext c; simp [hzw]
      rw [he]
      exact IsClosed.preimage ((continuous_apply z).prodMk (continuous_apply w))
        (isClosed_discrete _)
    · have he : {c : V → Fin n | G.Adj z w → c z ≠ c w} = Set.univ := by
        ext c; simp [hzw]
      rw [he]; exact isClosed_univ
  have hclosed : ∀ S, IsClosed (T S) := by
    intro S
    have he : T S = ⋂ z ∈ S, ⋂ w ∈ S, {c : V → Fin n | G.Adj z w → c z ≠ c w} := by
      ext c; simp [hT]
    rw [he]
    exact isClosed_biInter fun z _ => isClosed_biInter fun w _ => hpair z w
  have hdir : Directed (· ⊇ ·) T := by
    intro S1 S2
    refine ⟨S1 ∪ S2, ?_, ?_⟩ <;> intro c hc z hz w hw hadj <;>
      exact hc z (by simp [hz]) w (by simp [hw]) hadj
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hdir hne (fun S => (hclosed S).isCompact) hclosed
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro z w hadj
  have := Set.mem_iInter.mp hc ({z, w} : Finset V)
  exact this z (by simp) w (by simp) hadj

/-- The plane fails to be `4`-colourable **iff** some finite planar point set already
fails to be `4`-colourable. -/
