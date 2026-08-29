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

theorem runs_repeatLoop {ctr src dst : ℕ} (hcs : ctr ≠ src) (hcd : ctr ≠ dst)
    (hsd : src ≠ dst) (a : ℕ) :
    ∀ (s : Str) (r : Regs), r ctr = s → r src = List.replicate a true →
      Runs O (repeatLoop ctr src dst) r
        (Function.update
          (Function.update r dst (r dst ++ List.replicate (s.length * a) true)) ctr [])
        (s.length * (3 + a) + 1) := by
  intro s
  induction s with
  | nil =>
      intro r hctr hsrc d
      refine ⟨1, by simp, ?_⟩
      have hgoal : (Function.update (Function.update r dst (r dst ++
          List.replicate (([] : Str).length * a) true)) ctr []) = r := by
        funext j
        by_cases hj : j = ctr
        · subst hj; simp [Function.update_apply, hctr, Ne.symm hcd]
        · simp [Function.update_apply, hj]
      rw [hgoal]
      exact Exec.loopDone (c := ⟨r, d⟩) hctr
  | cons b t ih =>
      intro r hctr hsrc d
      have hsrclen : (r src).length = a := by rw [hsrc]; simp
      set r1 : Regs := Function.update r dst (r dst ++ r src) with hr1
      set r2 : Regs := Function.update r1 ctr (r1 ctr).tail with hr2
      have hr1ctr : r1 ctr = b :: t := by simp [hr1, Function.update_apply, hcd, hctr]
      have hr2ctr : r2 ctr = t := by simp [hr2, Function.update_apply, hr1ctr]
      have hr2src : r2 src = List.replicate a true := by
        simp [hr2, hr1, Function.update_apply, Ne.symm hcs, hsd, hsrc]
      have hr2dst : r2 dst = r dst ++ List.replicate a true := by
        simp [hr2, hr1, Function.update_apply, Ne.symm hcd, hsrc]
      have hr2other : ∀ j, j ≠ ctr → j ≠ dst → r2 j = r j := by
        intro j h1 h2
        simp [hr2, hr1, Function.update_apply, h1, h2]
      obtain ⟨n2, hn2, he2⟩ := ih r2 hr2ctr hr2src d
      have hbody : Exec O (Prog.seq (Prog.appendReg dst src) (Prog.pop ctr))
          ⟨r, d⟩ ⟨r2, d⟩ ((1 + (r src).length) + 1) [] := by
        have e1 : Exec O (Prog.appendReg dst src) ⟨r, d⟩ ⟨r1, d⟩ (1 + (r src).length) [] :=
          Exec.appendReg dst src ⟨r, d⟩
        have e2 : Exec O (Prog.pop ctr) ⟨r1, d⟩ ⟨r2, d⟩ 1 [] := Exec.pop ctr ⟨r1, d⟩
        exact Exec.seq e1 e2
      have hne : (⟨r, d⟩ : Cfg).regs ctr ≠ [] := by simp [hctr]
      refine ⟨1 + ((1 + (r src).length) + 1) + n2, ?_, ?_⟩
      · have hlen : (b :: t).length * (3 + a) = t.length * (3 + a) + (3 + a) := by
          simp [Nat.succ_mul]
        rw [hsrclen, hlen]
        linarith
      · have hgoal :
            (Function.update (Function.update r2 dst
              (r2 dst ++ List.replicate (t.length * a) true)) ctr []) =
            (Function.update (Function.update r dst
              (r dst ++ List.replicate ((b :: t).length * a) true)) ctr []) := by
          funext j
          by_cases hj : j = ctr
          · subst hj; simp
          · by_cases hj' : j = dst
            · subst hj'
              rw [Function.update_of_ne hj, Function.update_of_ne hj,
                Function.update_self, Function.update_self, hr2dst, List.append_assoc,
                ← List.replicate_add]
              congr 2
              rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
            · rw [Function.update_of_ne hj, Function.update_of_ne hj,
                Function.update_of_ne hj', Function.update_of_ne hj', hr2other j hj hj']
        rw [← hgoal]
        exact Exec.loopStep (c := ⟨r, d⟩) hne hbody he2


/-! ### Step wrappers, hiding the register updates -/

