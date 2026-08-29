import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Frontier

universe u

variable {V : Type u}

/-! ## Plane straight-line drawings

Mathlib (at the pinned commit) contains no theory of planar graphs at all, so we
first have to say what "planar" means.

We use the *straight-line* (Fáry) formulation: a finite simple graph is planar
exactly when it can be drawn in the plane with vertices at distinct points and
edges drawn as straight segments which meet only at shared endpoints.  By
Fáry's theorem this is equivalent to the usual topological definition for
finite simple graphs, and it has the advantage of being completely elementary
to state. -/

/-- The open straight segment in `ℝ²` drawn for an (unordered) edge `e`, when the
vertices are placed by `p`. -/

theorem exists_coloring_on [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hG : IsDegenerate G k) (s : Finset V) :
    ∃ c : V → ℕ, (∀ v, c v < k + 1) ∧ ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, fun _ => Nat.succ_pos k, by simp⟩
    obtain ⟨v, hv, hvcard⟩ := hG s hs
    obtain ⟨c, hc, hcol⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    -- the colours already used on the neighbours of `v` inside `s`
    set N : Finset V := (s.erase v).filter (fun u => G.Adj v u) with hN
    have hcardN : (N.image c).card ≤ k := le_trans (Finset.card_image_le) hvcard
    have hsub : ¬ (Finset.range (k + 1) ⊆ N.image c) := by
      intro hsub
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    obtain ⟨a, ha, hanot⟩ := Finset.not_subset.mp hsub
    refine ⟨Function.update c v a, ?_, ?_⟩
    · intro x
      by_cases hx : x = v
      · subst hx; simpa using Finset.mem_range.mp ha
      · simpa [Function.update_of_ne hx] using hc x
    · intro u hu w hw huw
      by_cases hu' : u = v
      · subst hu'
        have hwv : w ≠ u := (huw.ne).symm
        have hwN : w ∈ N := by
          simp only [hN, Finset.mem_filter, Finset.mem_erase]
          exact ⟨⟨hwv, hw⟩, huw⟩
        simp only [Function.update_of_ne hwv, Function.update_self]
        intro hcontra
        exact hanot (Finset.mem_image.mpr ⟨w, hwN, hcontra.symm⟩)
      · by_cases hw' : w = v
        · subst hw'
          have huw' : u ≠ w := huw.ne
          have huN : u ∈ N := by
            simp only [hN, Finset.mem_filter, Finset.mem_erase]
            exact ⟨⟨huw', hu⟩, huw.symm⟩
          simp only [Function.update_of_ne huw', Function.update_self]
          intro hcontra
          exact hanot (Finset.mem_image.mpr ⟨u, huN, hcontra⟩)
        · simp only [Function.update_of_ne hu', Function.update_of_ne hw']
          exact hcol u (Finset.mem_erase.mpr ⟨hu', hu⟩) w (Finset.mem_erase.mpr ⟨hw', hw⟩) huw

/-- A `k`-degenerate finite graph is `(k+1)`-colourable. -/
