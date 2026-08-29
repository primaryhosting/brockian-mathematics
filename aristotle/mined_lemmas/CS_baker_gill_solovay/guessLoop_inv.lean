import RequestProject.QueryProg
import RequestProject.Aux

/-!
# An oracle `A` with `P^A = NP^A`

The oracle answers questions about its own relativized nondeterministic
computations.  This is well defined because the query `encodeQ i x t` is *longer*
than any string that can be queried during a computation of cost at most `t` on
input `x`, so the definition can be made by recursion on the length of the query.
-/

namespace CS

open Prog

/-- `AAux n z` is the value of the oracle at `z`, where `n` is the length of `z`;
the recursive calls are only made at strictly shorter strings. -/

theorem guessLoop_inv (O : Oracle) : ∀ (s : Str) (r : Regs) (d : Str) (cfg : Cfg) (n : ℕ)
    (qs : List Str), r 3 = s → Exec O guessLoop ⟨r, d⟩ cfg n qs →
      qs = [] ∧ ∃ w : Str, w.length = s.length ∧ cfg.regs 2 = r 2 ++ w ∧
        ∀ j, j ≠ 2 → j ≠ 3 → cfg.regs j = r j := by
  intro s
  induction s with
  | nil =>
      intro r d cfg n qs h3 h
      cases h with
      | loopDone _ => exact ⟨rfl, [], by simp, by simp, fun j _ _ => rfl⟩
      | loopStep hne _ _ => exact absurd h3 hne
  | cons b t ih =>
      intro r d cfg n qs h3 h
      cases h with
      | loopDone hnil =>
          have hnil' : r 3 = [] := hnil
          rw [h3] at hnil'
          simp at hnil'
      | @loopStep _ _ _ c1 _ n1 n2 qs1 qs2 hne hbody hrest =>
          cases hbody with
          | @seq _ _ _ cmid _ _ _ _ _ hg hp =>
              cases hg with
              | @guess _ _ bb rest hcert =>
                  cases hp with
                  | pop _ _ =>
                      obtain ⟨hq2, w, hwlen, hw2, hwo⟩ := ih _ _ _ _ _
                        (by simp [Function.update_apply, h3]) hrest
                      refine ⟨by simp [hq2], bb :: w, by simp [hwlen], ?_, fun j h1 h2 => ?_⟩
                      · rw [hw2]
                        simp [Function.update_apply]
                      · rw [hwo j h1 h2]
                        simp [Function.update_apply, h1, h2]

