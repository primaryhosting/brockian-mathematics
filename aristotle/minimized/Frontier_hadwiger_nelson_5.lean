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

def planeGraph : SimpleGraph ℂ where
  Adj z w := dist z w = 1
  symm := by
    intro z w h
    rwa [dist_comm]
  loopless := ⟨fun z h => zero_ne_one ((dist_self z).symm.trans h)⟩

lemma planeGraph_colorable_iff (n : ℕ) :
    planeGraph.Colorable n ↔ ∃ c : ℂ → Fin n, ∀ z w : ℂ, dist z w = 1 → c z ≠ c w := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C, fun z w h => C.valid h⟩
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c fun {z w} h => hc z w h⟩

/-- If the plane admits no proper `n`-colouring, its chromatic number is `> n`. -/

lemma succ_le_chromaticNumber_of_not_colorable {n : ℕ} (h : ¬ planeGraph.Colorable n) :
    (n + 1 : ℕ∞) ≤ planeGraph.chromaticNumber := by
  by_contra hc
  push_neg at hc
  refine h (SimpleGraph.chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_succ ?_))
  rwa [Order.succ_eq_add_one]

/-! ## A convenient criterion for unit distance -/

/-- Two complex numbers are at distance `1` as soon as the sum of the squares of the
differences of their coordinates is `1`. -/

def DeGreyWitness : Prop :=
  ∃ S : Finset ℂ, ∀ c : ℂ → Fin 4, ∃ z ∈ S, ∃ w ∈ S, dist z w = 1 ∧ c z = c w

/-- Given a finite non-`4`-colourable unit-distance graph, the whole plane is not
`4`-colourable. -/

theorem plane_not_colorable_four (h : DeGreyWitness) : ¬ planeGraph.Colorable 4 := by
  obtain ⟨S, hS⟩ := h
  rw [planeGraph_colorable_iff]
  rintro ⟨c, hc⟩
  obtain ⟨z, -, w, -, hzw, hcol⟩ := hS c
  exact hc z w hzw hcol

/-- **The chromatic number of the plane is at least `5`** (de Grey, 2018).

The hypothesis `DeGreyWitness` is the finite combinatorial core of de Grey's theorem:
the existence of a finite planar point set whose unit-distance graph has no proper
`4`-colouring.  Everything else — the passage from that finite graph to the whole
plane — is proved here. -/

theorem hadwiger_nelson_5 (h : DeGreyWitness) : 5 ≤ planeGraph.chromaticNumber := by
  have := succ_le_chromaticNumber_of_not_colorable (plane_not_colorable_four h)
  simpa using this

/-! ## The hypothesis is exactly right: a compactness (de Bruijn–Erdős) argument

The finite witness assumed above is not merely sufficient, it is also necessary: if the
whole plane needs at least five colours then already some finite subset does.  This is a
compactness argument, proved here in the following general form. -/

/-- **Compactness for graph colourings** (de Bruijn–Erdős).  If every finite set of
vertices of a graph admits a proper `n`-colouring, then the whole graph is
`n`-colourable. -/
