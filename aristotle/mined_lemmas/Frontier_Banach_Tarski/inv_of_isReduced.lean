/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem inv_of_isReduced : ∀ L : List (Fin 2 × Bool), FreeGroup.IsReduced L → Inv L := by
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨by decide, ?_, ?_, ?_⟩ <;> simp
  | cons x L ih =>
      intro hred
      have hredL : FreeGroup.IsReduced L := hred.infix (List.suffix_cons x L).isInfix
      obtain ⟨hb, h0, h1, hnil⟩ := ih hredL
      have hfact0 : x.1 = 0 →
          ((stateOf L).1 + sgn x.2 * (stateOf L).2.1) % 3 = 0 ∨ (stateOf L).1 % 3 = 0 := by
        intro hx0
        cases L with
        | nil => exact Or.inr (hnil rfl).1
        | cons hd tl =>
            rcases fin2_cases hd.1 with hh | hh
            · have hhd : hd = ((0 : Fin 2), hd.2) := Prod.ext hh rfl
              have hx2 : x.2 = hd.2 := (FreeGroup.isReduced_cons_cons.mp hred).1 (by rw [hx0, hh])
              have hfin := h0 hd.2 (by rw [List.head?_cons, hhd])
              exact Or.inl (by rw [hx2]; exact hfin.1)
            · have hhd : hd = ((1 : Fin 2), hd.2) := Prod.ext hh rfl
              exact Or.inr (h1 hd.2 (by rw [List.head?_cons, hhd])).1
      have hfact1 : x.1 = 1 →
          ((stateOf L).2.2 - sgn x.2 * (stateOf L).2.1) % 3 = 0 ∨ (stateOf L).2.2 % 3 = 0 := by
        intro hx1
        cases L with
        | nil => exact Or.inr (hnil rfl).2
        | cons hd tl =>
            rcases fin2_cases hd.1 with hh | hh
            · have hhd : hd = ((0 : Fin 2), hd.2) := Prod.ext hh rfl
              exact Or.inr (h0 hd.2 (by rw [List.head?_cons, hhd])).2
            · have hhd : hd = ((1 : Fin 2), hd.2) := Prod.ext hh rfl
              have hx2 : x.2 = hd.2 := (FreeGroup.isReduced_cons_cons.mp hred).1 (by rw [hx1, hh])
              have hfin := h1 hd.2 (by rw [List.head?_cons, hhd])
              exact Or.inl (by rw [hx2]; exact hfin.2)
      rcases fin2_cases x.1 with hx | hx
      · have hs : stateOf (x :: L) = ((stateOf L).1 - 4 * sgn x.2 * (stateOf L).2.1,
            2 * sgn x.2 * (stateOf L).1 + (stateOf L).2.1, 3 * (stateOf L).2.2) := by
          rw [stateOf_cons, step, if_pos hx]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hs]
          exact arith1 _ _ _ (sgn_cases x.2) hb (hfact0 hx)
        · intro e he
          have hxe : x = ((0 : Fin 2), e) := Option.some_inj.mp (by rw [← List.head?_cons]; exact he)
          have hx2 : x.2 = e := by rw [hxe]
          rw [hs, ← hx2]
          exact arith2 _ _ _ _ (sgn_cases x.2)
        · intro e he
          have hxe : x = ((1 : Fin 2), e) := Option.some_inj.mp (by rw [← List.head?_cons]; exact he)
          rw [hxe] at hx
          simp at hx
        · intro hcon
          exact absurd hcon (List.cons_ne_nil _ _)
      · have hs : stateOf (x :: L) = (3 * (stateOf L).1,
            (stateOf L).2.1 - 2 * sgn x.2 * (stateOf L).2.2,
            4 * sgn x.2 * (stateOf L).2.1 + (stateOf L).2.2) := by
          rw [stateOf_cons, step, if_neg (by rw [hx]; decide)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hs]
          exact arith3 _ _ _ (sgn_cases x.2) hb (hfact1 hx)
        · intro e he
          have hxe : x = ((0 : Fin 2), e) := Option.some_inj.mp (by rw [← List.head?_cons]; exact he)
          rw [hxe] at hx
          simp at hx
        · intro e he
          have hxe : x = ((1 : Fin 2), e) := Option.some_inj.mp (by rw [← List.head?_cons]; exact he)
          have hx2 : x.2 = e := by rw [hxe]
          rw [hs, ← hx2]
          exact arith4 _ _ _ _ (sgn_cases x.2)
        · intro hcon
          exact absurd hcon (List.cons_ne_nil _ _)

/-! ### Freeness -/

