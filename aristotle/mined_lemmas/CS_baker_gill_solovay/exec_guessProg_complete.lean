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

theorem exec_guessProg_complete (O : Oracle) (x w : Str) (hw : w.length = x.length) :
    ∃ (cfg : Cfg) (n : ℕ), n ≤ 6 * (x.length + 1) ∧
      Exec O guessProg (initCfg x w) cfg n [w] ∧ (cfg.regs 1 = [true] ↔ O w) := by
  classical
  set r : Regs := (initCfg x w).regs with hrdef
  have hr0 : r 0 = x := by simp [hrdef, initCfg]
  have hr1 : r 1 = [] := by simp [hrdef, initCfg]
  obtain ⟨r1, e1, v1, o1⟩ := step_clear O r 3
  obtain ⟨r2, e2, v2, o2⟩ := step_appendReg O r1 3 0
  obtain ⟨r3, e3, v3, o3⟩ := step_clear O r2 2
  have h20 : r2 0 = x := by rw [o2 0 (by decide), o1 0 (by decide), hr0]
  have h21 : r2 1 = [] := by rw [o2 1 (by decide), o1 1 (by decide), hr1]
  have h23 : r2 3 = x := by rw [v2, v1, o1 0 (by decide), hr0]; simp
  have h33 : r3 3 = x := by rw [o3 3 (by decide), h23]
  have h32 : r3 2 = [] := v3
  have h31 : r3 1 = [] := by rw [o3 1 (by decide), h21]
  obtain ⟨r4, hloop, w2, w3, wo⟩ :=
    exec_guessLoop O x w r3 [] h33 hw
  have h42 : r4 2 = w := by rw [w2, h32]; simp
  have h41 : r4 1 = [] := by rw [wo 1 (by decide) (by decide), h31]
  have hcert : (w ++ ([] : Str)) = w := by simp
  rw [hcert] at hloop
  by_cases hO : O (r4 2)
  · have eqy : Exec O (Prog.query 1 2) ⟨r4, ([] : Str)⟩
        ⟨Function.update r4 1 (r4 1 ++ [true]), ([] : Str)⟩ (1 + (r4 2).length) [r4 2] :=
      Exec.queryT (c := ⟨r4, ([] : Str)⟩) hO
    have hlq : Exec O (Prog.seq guessLoop (Prog.query 1 2)) ⟨r3, w⟩
        ⟨Function.update r4 1 (r4 1 ++ [true]), ([] : Str)⟩
        ((3 * x.length + 1) + (1 + (r4 2).length)) ([] ++ [r4 2]) := Exec.seq hloop eqy
    obtain ⟨n3, hn3, f3⟩ := e3.seqExec hlq
    obtain ⟨n2, hn2, f2⟩ := e2.seqExec f3
    obtain ⟨n1, hn1, f1⟩ := e1.seqExec f2
    refine ⟨⟨Function.update r4 1 (r4 1 ++ [true]), ([] : Str)⟩, n1, ?_, ?_, ?_⟩
    · have q1 : (r1 0).length = x.length := by rw [o1 0 (by decide), hr0]
      have q2 : (r4 2).length = x.length := by rw [h42, hw]
      rw [q2] at hn3
      rw [q1] at hn2
      omega
    · have : ([] ++ [r4 2]) = [w] := by simp [h42]
      rw [← this]
      exact f1
    · rw [h42] at hO
      simp [h41, hO]
  · have eqn : Exec O (Prog.query 1 2) ⟨r4, ([] : Str)⟩
        ⟨Function.update r4 1 (r4 1 ++ [false]), ([] : Str)⟩ (1 + (r4 2).length) [r4 2] :=
      Exec.queryF (c := ⟨r4, ([] : Str)⟩) hO
    have hlq : Exec O (Prog.seq guessLoop (Prog.query 1 2)) ⟨r3, w⟩
        ⟨Function.update r4 1 (r4 1 ++ [false]), ([] : Str)⟩
        ((3 * x.length + 1) + (1 + (r4 2).length)) ([] ++ [r4 2]) := Exec.seq hloop eqn
    obtain ⟨n3, hn3, f3⟩ := e3.seqExec hlq
    obtain ⟨n2, hn2, f2⟩ := e2.seqExec f3
    obtain ⟨n1, hn1, f1⟩ := e1.seqExec f2
    refine ⟨⟨Function.update r4 1 (r4 1 ++ [false]), ([] : Str)⟩, n1, ?_, ?_, ?_⟩
    · have q1 : (r1 0).length = x.length := by rw [o1 0 (by decide), hr0]
      have q2 : (r4 2).length = x.length := by rw [h42, hw]
      rw [q2] at hn3
      rw [q1] at hn2
      omega
    · have : ([] ++ [r4 2]) = [w] := by simp [h42]
      rw [← this]
      exact f1
    · simp only [Function.update_self, h41, List.nil_append]
      rw [h42] at hO
      simp [hO]

/-- Inversion for the guessing loop: whatever the certificate, the loop appends to
register `2` a string of the same length as register `3`. -/
