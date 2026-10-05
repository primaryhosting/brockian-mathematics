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

theorem runs_mulBlock (O : Oracle) (r : Regs) (a : ℕ) (h4 : r 4 = List.replicate a true) :
    ∃ r' : Regs, Runs O mulBlock r r' (8 * ((r 0).length + 1) * (a + 1)) ∧
      r' 4 = List.replicate (((r 0).length + 2) * a) true ∧
      r' 0 = r 0 ∧ r' 1 = r 1 ∧ r' 2 = r 2 := by
  obtain ⟨r1, e1, v1, o1⟩ := step_clear O r 5
  obtain ⟨r2, e2, v2, o2⟩ := step_appendReg O r1 5 4
  obtain ⟨r3, e3, v3, o3⟩ := step_clear O r2 4
  obtain ⟨r4, e4, v4, o4⟩ := step_clear O r3 3
  obtain ⟨r5, e5, v5, o5⟩ := step_appendReg O r4 3 0
  have h14 : r1 4 = List.replicate a true := by rw [o1 4 (by decide), h4]
  have h10 : r1 0 = r 0 := o1 0 (by decide)
  have h25 : r2 5 = List.replicate a true := by rw [v2, v1, h14]; simp
  have h24 : r2 4 = List.replicate a true := by rw [o2 4 (by decide), h14]
  have h20 : r2 0 = r 0 := by rw [o2 0 (by decide), h10]
  have h35 : r3 5 = List.replicate a true := by rw [o3 5 (by decide), h25]
  have h34 : r3 4 = [] := v3
  have h30 : r3 0 = r 0 := by rw [o3 0 (by decide), h20]
  have h45 : r4 5 = List.replicate a true := by rw [o4 5 (by decide), h35]
  have h44 : r4 4 = [] := by rw [o4 4 (by decide), h34]
  have h40 : r4 0 = r 0 := by rw [o4 0 (by decide), h30]
  have h43 : r4 3 = [] := v4
  have h55 : r5 5 = List.replicate a true := by rw [o5 5 (by decide), h45]
  have h54 : r5 4 = [] := by rw [o5 4 (by decide), h44]
  have h50 : r5 0 = r 0 := by rw [o5 0 (by decide), h40]
  have h53 : r5 3 = r 0 := by rw [v5, h43, h40]; simp
  obtain ⟨r6, e6, v6, v6c, o6⟩ := step_repeatLoop O r5 (by decide : (3:ℕ) ≠ 5)
    (by decide : (3:ℕ) ≠ 4) (by decide : (5:ℕ) ≠ 4) a h55
  obtain ⟨r7, e7, v7, o7⟩ := step_appendReg O r6 4 5
  obtain ⟨r8, e8, v8, o8⟩ := step_appendReg O r7 4 5
  have h64 : r6 4 = List.replicate ((r 0).length * a) true := by
    rw [v6, h54, h53]; simp
  have h65 : r6 5 = List.replicate a true := by rw [o6 5 (by decide) (by decide), h55]
  have h74 : r7 4 = List.replicate (((r 0).length + 1) * a) true := by
    rw [v7, h64, h65, ← List.replicate_add]
    congr 1
    ring
  have h75 : r7 5 = List.replicate a true := by rw [o7 5 (by decide), h65]
  have h84 : r8 4 = List.replicate (((r 0).length + 2) * a) true := by
    rw [v8, h74, h75, ← List.replicate_add]
    congr 1
    ring
  refine ⟨r8, ?_, h84, ?_, ?_, ?_⟩
  · have hchain := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
    unfold mulBlock
    refine hchain.mono ?_
    have q1 : (r1 4).length = a := by rw [h14]; simp
    have q2 : (r4 0).length = (r 0).length := by rw [h40]
    have q3 : (r5 3).length = (r 0).length := by rw [h53]
    have q4 : (r6 5).length = a := by rw [h65]; simp
    have q5 : (r7 5).length = a := by rw [h75]; simp
    rw [q1, q2, q3, q4, q5]
    nlinarith [Nat.zero_le ((r 0).length), Nat.zero_le a]
  · rw [o8 0 (by decide), o7 0 (by decide), o6 0 (by decide) (by decide), h50]
  · rw [o8 1 (by decide), o7 1 (by decide), o6 1 (by decide) (by decide),
      o5 1 (by decide), o4 1 (by decide), o3 1 (by decide), o2 1 (by decide),
      o1 1 (by decide)]
  · rw [o8 2 (by decide), o7 2 (by decide), o6 2 (by decide) (by decide),
      o5 2 (by decide), o4 2 (by decide), o3 2 (by decide), o2 2 (by decide),
      o1 2 (by decide)]

/-- `padProg m` puts the string `1 ^ ((|x| + 2) ^ m)` into register `4`. -/
