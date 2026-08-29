/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/

theorem ustconBP_run [NeZero D] (hk : 0 < k) (nbr : Fin n → Fin D → Fin n) (s t : Fin n)
    (l : ℕ) :
    ((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l).1
        = walk nbr s (dig D (l / k)) (l % k)
      ∧ ((((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l).2 = true)
        ↔ (s = t ∨ ∃ l' < l, walk nbr s (dig D (l' / k)) (l' % k + 1) = t)) := by
  induction l with
  | zero =>
      simp [BP.run, ustconBP, walk, Nat.zero_div, Nat.zero_mod]
  | succ l ih =>
      obtain ⟨ih1, ih2⟩ := ih
      obtain ⟨hm, hd⟩ := div_mod_succ (k := k) hk l
      have hstep : (ustconBP n D k s t).run (fun q => nbr q.1 q.2) (l + 1)
          = ((if (l + 1) % k = 0 then s else walk nbr s (dig D (l / k)) (l % k + 1)),
             ((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l).2
                || decide (walk nbr s (dig D (l / k)) (l % k + 1) = t)) := by
        have e1 : (ustconBP n D k s t).run (fun q => nbr q.1 q.2) (l + 1)
            = (ustconBP n D k s t).next l ((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l)
                (nbr (((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l).1)
                  (dig D (l / k) (l % k))) := rfl
        rw [e1, ih1]
        rfl
      refine ⟨?_, ?_⟩
      · rw [hstep]
        by_cases h : (l + 1) % k = 0
        · rw [if_pos h, h]
          rfl
        · have hlt : l % k + 1 < k := by
            rcases Nat.lt_or_ge (l % k + 1) k with h' | h'
            · exact h'
            · exfalso
              have : l % k + 1 = k := le_antisymm (Nat.succ_le_of_lt (Nat.mod_lt _ hk)) h'
              rw [hm, this, Nat.mod_self] at h
              exact h rfl
          have h1 : (l + 1) % k = l % k + 1 := by
            rw [hm, Nat.mod_eq_of_lt hlt]
          have h2 : (l + 1) / k = l / k := by
            rw [hd, Nat.div_eq_of_lt hlt, Nat.zero_add]
          rw [h1, h2, if_neg (by omega)]
      · rw [hstep]
        simp only [Bool.or_eq_true, decide_eq_true_eq, ih2]
        constructor
        · rintro ((h | ⟨l', hl', hw⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨l', by omega, hw⟩
          · exact Or.inr ⟨l, by omega, h⟩
        · rintro (h | ⟨l', hl', hw⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge l' l with h' | h'
            · exact Or.inl (Or.inr ⟨l', h', hw⟩)
            · have : l' = l := by omega
              subst this
              exact Or.inr hw

