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

theorem exec_guessLoop (O : Oracle) : ∀ (s w : Str) (r : Regs) (d : Str),
    r 3 = s → w.length = s.length →
      ∃ r' : Regs, Exec O guessLoop ⟨r, w ++ d⟩ ⟨r', d⟩ (3 * s.length + 1) [] ∧
        r' 2 = r 2 ++ w ∧ r' 3 = [] ∧ ∀ j, j ≠ 2 → j ≠ 3 → r' j = r j := by
  intro s
  induction s with
  | nil =>
      intro w r d h3 hw
      have hwnil : w = [] := List.length_eq_zero_iff.1 (by simpa using hw)
      subst hwnil
      refine ⟨r, ?_, by simp, h3, fun j _ _ => rfl⟩
      simpa using Exec.loopDone (O := O) (body := Prog.seq (Prog.guess 2) (Prog.pop 3))
        (c := ⟨r, [] ++ d⟩) h3
  | cons b t ih =>
      intro w r d h3 hw
      obtain ⟨c, v, rfl⟩ : ∃ (c : Bool) (v : Str), w = c :: v := by
        cases w with
        | nil => simp at hw
        | cons c v => exact ⟨c, v, rfl⟩
      have hv : v.length = t.length := by simpa using hw
      set r1 : Regs := Function.update r 2 (r 2 ++ [c]) with hr1
      set r2 : Regs := Function.update r1 3 (r1 3).tail with hr2
      have hr13 : r1 3 = b :: t := by simp [hr1, Function.update_apply, h3]
      have hr23 : r2 3 = t := by simp [hr2, Function.update_apply, hr13]
      have hr22 : r2 2 = r 2 ++ [c] := by simp [hr2, hr1, Function.update_apply]
      have hr2other : ∀ j, j ≠ 2 → j ≠ 3 → r2 j = r j := by
        intro j h1 h2
        simp [hr2, hr1, Function.update_apply, h1, h2]
      obtain ⟨r', he, v2, v3, vo⟩ := ih v r2 d hr23 hv
      have hguess : Exec O (Prog.guess 2) ⟨r, (c :: v) ++ d⟩ ⟨r1, v ++ d⟩ 1 [] :=
        Exec.guess (i := 2) (c := ⟨r, (c :: v) ++ d⟩) rfl
      have hpop : Exec O (Prog.pop 3) ⟨r1, v ++ d⟩ ⟨r2, v ++ d⟩ 1 [] :=
        Exec.pop 3 ⟨r1, v ++ d⟩
      have hbody : Exec O (Prog.seq (Prog.guess 2) (Prog.pop 3))
          ⟨r, (c :: v) ++ d⟩ ⟨r2, v ++ d⟩ 2 [] := by
        simpa using Exec.seq hguess hpop
      have hne : (⟨r, (c :: v) ++ d⟩ : Cfg).regs 3 ≠ [] := by simp [h3]
      refine ⟨r', ?_, ?_, v3, fun j h1 h2 => ?_⟩
      · have hstep := Exec.loopStep (c := ⟨r, (c :: v) ++ d⟩) hne hbody he
        have harith : 1 + 2 + (3 * t.length + 1) = 3 * (b :: t).length + 1 := by
          simp [List.length_cons]
          omega
        simpa [harith] using hstep
      · rw [v2, hr22, List.append_assoc]
        rfl
      · rw [vo j h1 h2, hr2other j h1 h2]

