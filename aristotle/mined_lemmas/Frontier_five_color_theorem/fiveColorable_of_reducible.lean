import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

theorem fiveColorable_of_reducible :
    ∀ (n : ℕ) (s : Finset V) (G : SimpleGraph V), s.card ≤ n → FiveColorReducible s G →
      FiveColorable s G := by
  intro n
  induction n with
  | zero =>
      intro s G hs _
      have : s = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hs)
      subst this
      exact ⟨fun _ => 0, by simp [IsProperColoring]⟩
  | succ n ih =>
      intro s G hs hgood
      rcases Finset.eq_empty_or_nonempty s with rfl | hne
      · exact ⟨fun _ => 0, by simp [IsProperColoring]⟩
      obtain ⟨v, hv, hcase⟩ := hgood s G (Reduces.refl s G) hne
      rcases hcase with hdeg | ⟨hdeg, u, hu, w, hw, huw, hnadj⟩
      · -- Case A: `v` has at most four neighbours; delete it.
        have hcard : (s.erase v).card ≤ n := by
          have := Finset.card_erase_of_mem hv
          omega
        have hgood' : FiveColorReducible (s.erase v) G := by
          intro t H hred
          exact hgood t H (Reduces.del v hred)
        obtain ⟨c', hc'⟩ := ih (s.erase v) G hcard hgood'
        obtain ⟨f, hf⟩ := exists_free_color (nbrs s G v) c' hdeg
        refine ⟨Function.update c' v f, ?_⟩
        intro x hx y hy hadj
        by_cases hxv : x = v
        · subst hxv
          have hyx : y ≠ x := (hadj.ne).symm
          have hy' : y ∈ nbrs s G x := mem_nbrs.2 ⟨hy, hyx, hadj⟩
          simp only [Function.update_apply, if_neg hyx]
          exact fun h => hf y hy' h.symm
        · by_cases hyv : y = v
          · subst hyv
            have hxy : x ≠ y := hadj.ne
            have hx' : x ∈ nbrs s G y := mem_nbrs.2 ⟨hx, hxy, hadj.symm⟩
            simp only [Function.update_apply, if_neg hxy]
            exact fun h => hf x hx' h
          · simp only [Function.update_apply, if_neg hxv, if_neg hyv]
            exact hc' x (Finset.mem_erase.2 ⟨hxv, hx⟩) y (Finset.mem_erase.2 ⟨hyv, hy⟩) hadj
      · -- Case B: `v` has five neighbours, two of which, `u` and `w`, are non-adjacent.
        obtain ⟨hus, huv, hadjvu⟩ := mem_nbrs.1 hu
        obtain ⟨hws, hwv, hadjvw⟩ := mem_nbrs.1 hw
        set s' : Finset V := (s.erase v).erase w with hs'
        set G' : SimpleGraph V := contract G u w with hG'
        have hcard : s'.card ≤ n := by
          have h1 := Finset.card_erase_of_mem hv
          have h2 : s'.card ≤ (s.erase v).card := Finset.card_erase_le
          omega
        have hgood' : FiveColorReducible s' G' := by
          intro t H hred
          exact hgood t H (Reduces.con v u w hu hw huw hnadj hred)
        obtain ⟨c', hc'⟩ := ih s' G' hcard hgood'
        -- first give `w` the colour of `u`
        set c₀ : V → Fin 5 := Function.update c' w (c' u) with hc₀
        have hc₀u : c₀ u = c' u := by simp [hc₀, huw]
        have hc₀w : c₀ w = c' u := by simp [hc₀]
        have hc₀other : ∀ x, x ≠ w → c₀ x = c' x := by
          intro x hx; simp [hc₀, hx]
        have hus' : u ∈ s' := by
          simp only [hs', Finset.mem_erase]
          exact ⟨huw, huv, hus⟩
        -- the colours used on the neighbourhood of `v` : at most four of them
        have hsub : ((nbrs s G v).erase w).card ≤ 4 := by
          have := Finset.card_erase_of_mem hw
          omega
        obtain ⟨f, hf⟩ := exists_free_color ((nbrs s G v).erase w) c₀ hsub
        have hfree : ∀ y ∈ nbrs s G v, c₀ y ≠ f := by
          intro y hy
          by_cases hyw : y = w
          · subst hyw
            rw [hc₀w, ← hc₀u]
            exact hf u (Finset.mem_erase.2 ⟨huw, hu⟩)
          · exact hf y (Finset.mem_erase.2 ⟨hyw, hy⟩)
        refine ⟨Function.update c₀ v f, ?_⟩
        have key : ∀ x ∈ s, ∀ y ∈ s, x ≠ v → y ≠ v → G.Adj x y → c₀ x ≠ c₀ y := by
          intro x hx y hy hxv hyv hadj
          by_cases hxw : x = w
          · subst hxw
            have hyx : y ≠ x := (hadj.ne).symm
            have hyu : y ≠ u := by
              rintro rfl
              exact hnadj (hadj.symm)
            have hy' : y ∈ s' := by
              simp only [hs', Finset.mem_erase]
              exact ⟨hyx, hyv, hy⟩
            have hadj' : G'.Adj u y := by
              refine ⟨Ne.symm hyu, ?_⟩
              right; left; exact ⟨rfl, hadj⟩
            rw [hc₀w, hc₀other y hyx]
            exact hc' u hus' y hy' hadj'
          · by_cases hyw : y = w
            · subst hyw
              have hxy : x ≠ y := hadj.ne
              have hxu : x ≠ u := by
                rintro rfl
                exact hnadj hadj
              have hx' : x ∈ s' := by
                simp only [hs', Finset.mem_erase]
                exact ⟨hxy, hxv, hx⟩
              have hadj' : G'.Adj x u := by
                refine ⟨hxu, ?_⟩
                right; right; exact ⟨rfl, hadj.symm⟩
              rw [hc₀w, hc₀other x hxy]
              exact hc' x hx' u hus' hadj'
            · have hx' : x ∈ s' := by
                simp only [hs', Finset.mem_erase]
                exact ⟨hxw, hxv, hx⟩
              have hy' : y ∈ s' := by
                simp only [hs', Finset.mem_erase]
                exact ⟨hyw, hyv, hy⟩
              have hadj' : G'.Adj x y := ⟨hadj.ne, Or.inl hadj⟩
              rw [hc₀other x hxw, hc₀other y hyw]
              exact hc' x hx' y hy' hadj'
        intro x hx y hy hadj
        by_cases hxv : x = v
        · subst hxv
          have hyx : y ≠ x := (hadj.ne).symm
          have hy' : y ∈ nbrs s G x := mem_nbrs.2 ⟨hy, hyx, hadj⟩
          simp only [Function.update_apply, if_neg hyx]
          exact fun h => hfree y hy' h.symm
        · by_cases hyv : y = v
          · subst hyv
            have hxy : x ≠ y := hadj.ne
            have hx' : x ∈ nbrs s G y := mem_nbrs.2 ⟨hx, hxy, hadj.symm⟩
            simp only [Function.update_apply, if_neg hxy]
            exact fun h => hfree x hx' h
          · simp only [Function.update_apply, if_neg hxv, if_neg hyv]
            exact key x hx y hy hxv hyv hadj

/-- **Five Colour Theorem** (combinatorial core).  Every finite graph satisfying the
planarity-derived reduction hypothesis `FiveColorReducible` is `5`-colourable. -/
