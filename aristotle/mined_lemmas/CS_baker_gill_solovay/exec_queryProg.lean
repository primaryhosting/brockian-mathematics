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

theorem exec_queryProg (O : Oracle) (i m : ℕ) (x d : Str) :
    ∃ (cfg : Cfg) (nn : ℕ), nn ≤ qCost i m x.length ∧
      Exec O (queryProg i m) (initCfg x d) cfg nn [encodeQ i x ((x.length + 2) ^ m)] ∧
      (cfg.regs 1 = [true] ↔ O (encodeQ i x ((x.length + 2) ^ m))) := by
  classical
  set t := (x.length + 2) ^ m with ht
  set r : Regs := (initCfg x d).regs with hrdef
  have hr0 : r 0 = x := by simp [hrdef, initCfg]
  have hr1 : r 1 = [] := by simp [hrdef, initCfg]
  have hr2 : r 2 = [] := by simp [hrdef, initCfg]
  obtain ⟨r1, e1, v1, u0, u1, u2⟩ := runs_padProg O m r
  rw [hr0] at v1 u0
  obtain ⟨r2, e2, v2, o2⟩ := step_clear O r1 2
  obtain ⟨r3, e3, v3, o3⟩ := step_appendReg O r2 2 4
  obtain ⟨r4, e4, v4, o4⟩ := step_appendBit O r3 2 false
  obtain ⟨r5, e5, v5, o5⟩ := step_appendConst O r4 2 (List.replicate i true)
  obtain ⟨r6, e6, v6, o6⟩ := step_appendBit O r5 2 false
  obtain ⟨r7, e7, v7, o7⟩ := step_appendReg O r6 2 0
  -- values of the registers along the way
  have h24 : r2 4 = List.replicate t true := by rw [o2 4 (by decide), v1]
  have h20 : r2 0 = x := by rw [o2 0 (by decide), u0]
  have h21 : r2 1 = [] := by rw [o2 1 (by decide), u1, hr1]
  have h32 : r3 2 = List.replicate t true := by rw [v3, v2, h24]; simp
  have h30 : r3 0 = x := by rw [o3 0 (by decide), h20]
  have h31 : r3 1 = [] := by rw [o3 1 (by decide), h21]
  have h42 : r4 2 = List.replicate t true ++ [false] := by rw [v4, h32]
  have h40 : r4 0 = x := by rw [o4 0 (by decide), h30]
  have h41 : r4 1 = [] := by rw [o4 1 (by decide), h31]
  have h52 : r5 2 = List.replicate t true ++ [false] ++ List.replicate i true := by
    rw [v5, h42]
  have h50 : r5 0 = x := by rw [o5 0 (by decide), h40]
  have h51 : r5 1 = [] := by rw [o5 1 (by decide), h41]
  have h62 : r6 2 = List.replicate t true ++ [false] ++ List.replicate i true ++ [false] := by
    rw [v6, h52]
  have h60 : r6 0 = x := by rw [o6 0 (by decide), h50]
  have h61 : r6 1 = [] := by rw [o6 1 (by decide), h51]
  have h72 : r7 2 = encodeQ i x t := by
    rw [v7, h62, h60]
    simp [encodeQ]
  have h71 : r7 1 = [] := by rw [o7 1 (by decide), h61]
  -- the final query
  have hlen : (r7 2).length = t + 1 + i + 1 + x.length := by rw [h72, encodeQ_length]
  by_cases hO : O (r7 2)
  · have eq : Exec O (Prog.query 1 2) ⟨r7, d⟩
        ⟨Function.update r7 1 (r7 1 ++ [true]), d⟩ (1 + (r7 2).length) [r7 2] :=
      Exec.queryT (c := ⟨r7, d⟩) hO
    obtain ⟨n7, hn7, f7⟩ := e7.seqExec eq
    obtain ⟨n6, hn6, f6⟩ := e6.seqExec f7
    obtain ⟨n5, hn5, f5⟩ := e5.seqExec f6
    obtain ⟨n4, hn4, f4⟩ := e4.seqExec f5
    obtain ⟨n3, hn3, f3⟩ := e3.seqExec f4
    obtain ⟨n2, hn2, f2⟩ := e2.seqExec f3
    obtain ⟨n1, hn1, f1⟩ := e1.seqExec f2
    refine ⟨⟨Function.update r7 1 (r7 1 ++ [true]), d⟩, n1, ?_, ?_, ?_⟩
    · have q1 : (r2 4).length = t := by rw [h24]; simp
      have q2 : (r6 0).length = x.length := by rw [h60]
      have q3 : (List.replicate i true).length = i := by simp
      rw [hlen, q2] at hn7
      rw [q3] at hn5
      rw [q1] at hn3
      rw [hr0] at hn1
      simp only [qCost, ← ht]
      omega
    · rw [← h72]
      exact f1
    · simp [h71, ← h72, hO]
  · have eq : Exec O (Prog.query 1 2) ⟨r7, d⟩
        ⟨Function.update r7 1 (r7 1 ++ [false]), d⟩ (1 + (r7 2).length) [r7 2] :=
      Exec.queryF (c := ⟨r7, d⟩) hO
    obtain ⟨n7, hn7, f7⟩ := e7.seqExec eq
    obtain ⟨n6, hn6, f6⟩ := e6.seqExec f7
    obtain ⟨n5, hn5, f5⟩ := e5.seqExec f6
    obtain ⟨n4, hn4, f4⟩ := e4.seqExec f5
    obtain ⟨n3, hn3, f3⟩ := e3.seqExec f4
    obtain ⟨n2, hn2, f2⟩ := e2.seqExec f3
    obtain ⟨n1, hn1, f1⟩ := e1.seqExec f2
    refine ⟨⟨Function.update r7 1 (r7 1 ++ [false]), d⟩, n1, ?_, ?_, ?_⟩
    · have q1 : (r2 4).length = t := by rw [h24]; simp
      have q2 : (r6 0).length = x.length := by rw [h60]
      have q3 : (List.replicate i true).length = i := by simp
      rw [hlen, q2] at hn7
      rw [q3] at hn5
      rw [q1] at hn3
      rw [hr0] at hn1
      simp only [qCost, ← ht]
      omega
    · rw [← h72]
      exact f1
    · simp [h71, ← h72, hO]

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

