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
def AAux (n : ℕ) : Str → Prop :=
  fun z => ∃ (i : ℕ) (x : Str) (t : ℕ), z = encodeQ i x t ∧
    ∃ cert : Str, AcceptsWithin
      (fun y => if _h : y.length < n then AAux y.length y else False) (progOf i) x cert t
termination_by n
decreasing_by exact ‹_›

/-- The self-referential oracle `A`. -/
def oracleA : Oracle := fun z => AAux z.length z

theorem shortA_eq (n : ℕ) :
    (fun y : Str => if _h : y.length < n then AAux y.length y else False)
      = (fun y : Str => y.length < n ∧ oracleA y) := by
  funext y
  by_cases h : y.length < n
  · simp [h, oracleA]
  · simp [h]

theorem AAux_iff (n : ℕ) (z : Str) :
    AAux n z ↔ ∃ (i : ℕ) (x : Str) (t : ℕ), z = encodeQ i x t ∧
      ∃ cert : Str, AcceptsWithin (fun y => y.length < n ∧ oracleA y) (progOf i) x cert t := by
  rw [AAux, shortA_eq]

/-- Restricting the oracle to short strings does not change computations which are
too short to ask long questions. -/
theorem acceptsWithin_short_iff (i : ℕ) (x : Str) (t N : ℕ) (hN : x.length + t < N) :
    (∃ cert, AcceptsWithin (fun y => y.length < N ∧ oracleA y) (progOf i) x cert t) ↔
      (∃ cert, AcceptsWithin oracleA (progOf i) x cert t) := by
  constructor
  · rintro ⟨cert, cfg, n, qs, hn, hex, hacc⟩
    refine ⟨cert, cfg, n, qs, hn, hex.locality ?_, hacc⟩
    intro s hs
    have hlen : s.length ≤ x.length + n := query_len_bound hex s hs
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  · rintro ⟨cert, cfg, n, qs, hn, hex, hacc⟩
    refine ⟨cert, cfg, n, qs, hn, hex.locality ?_, hacc⟩
    intro s hs
    have hlen : s.length ≤ x.length + n := query_len_bound hex s hs
    exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

/-- The defining property of `A`. -/
theorem oracleA_query (i m : ℕ) (x : Str) :
    oracleA (encodeQ i x ((x.length + 2) ^ m)) ↔
      ∃ cert, AcceptsWithin oracleA (progOf i) x cert ((x.length + 2) ^ m) := by
  set t := (x.length + 2) ^ m with ht
  have hlen : (encodeQ i x t).length = t + 1 + i + 1 + x.length := encodeQ_length i x t
  have hN : x.length + t < (encodeQ i x t).length := by rw [hlen]; omega
  rw [show oracleA (encodeQ i x t) = AAux (encodeQ i x t).length (encodeQ i x t) from rfl,
    AAux_iff]
  constructor
  · rintro ⟨i', x', t', heq, hrun⟩
    obtain ⟨rfl, rfl, rfl⟩ := encodeQ_inj heq.symm
    exact (acceptsWithin_short_iff _ _ _ _ hN).1 hrun
  · intro h
    exact ⟨i, x, t, rfl, (acceptsWithin_short_iff i x t _ hN).2 h⟩

/-- Every language in `NP^A` is in `P^A`: a single query to `A` decides it. -/
theorem NPClass_oracleA_subset_PClass : NPClass oracleA ⊆ PClass oracleA := by
  rintro L ⟨p, m, hL⟩
  obtain ⟨i, rfl⟩ := progOf_surjective p
  obtain ⟨m', hm'⟩ := polyBdd_le_pow (polyBdd_qCost i m)
  refine ⟨queryProg i m, m', noGuess_queryProg i m, ?_, ?_⟩
  · intro O' x
    obtain ⟨cfg, nn, hnn, hex, -⟩ := exec_queryProg O' i m x []
    exact ⟨cfg, nn, _, le_trans hnn (hm' x.length), hex⟩
  · intro x
    obtain ⟨cfg, nn, hnn, hex, hiff⟩ := exec_queryProg oracleA i m x []
    rw [hL x]
    constructor
    · intro h
      exact ⟨cfg, nn, _, le_trans hnn (hm' x.length), hex,
        hiff.2 ((oracleA_query i m x).2 h)⟩
    · rintro ⟨cfg2, n2, qs2, hn2, hex2, hacc2⟩
      obtain ⟨rfl, -, -⟩ := hex2.det cfg nn _ hex (noGuess_queryProg i m)
      exact (oracleA_query i m x).1 (hiff.1 hacc2)

/-- **First half of Baker–Gill–Solovay**: there is an oracle relative to which
`P` and `NP` coincide. -/
theorem exists_oracle_P_eq_NP : ∃ A : Oracle, PClass A = NPClass A :=
  ⟨oracleA, Set.Subset.antisymm (PClass_subset_NPClass oracleA)
    NPClass_oracleA_subset_PClass⟩

end CS

import RequestProject.Model

/-!
# Programming gadgets

Concrete programs of the model of `RequestProject.Model`, together with their
behaviour and running time.
-/

namespace CS

open Prog

/-- `Runs O p r r' T`: from register file `r`, the program `p` terminates with
register file `r'`, asking no oracle queries, at cost at most `T` (for every
value of the guess string, which is left untouched). -/
def Runs (O : Oracle) (p : Prog) (r r' : Regs) (T : ℕ) : Prop :=
  ∀ d : Str, ∃ n ≤ T, Exec O p ⟨r, d⟩ ⟨r', d⟩ n []

variable {O : Oracle} {p q : Prog} {r r' r'' : Regs} {T T' : ℕ}

theorem Runs.mono (h : Runs O p r r' T) (hT : T ≤ T') : Runs O p r r' T' := by
  intro d
  obtain ⟨n, hn, hex⟩ := h d
  exact ⟨n, hn.trans hT, hex⟩

theorem Runs.congr (h : Runs O p r r' T) (he : r' = r'') : Runs O p r r'' T := he ▸ h

theorem runs_done (r : Regs) : Runs O Prog.done r r 1 := fun d => ⟨1, le_rfl, Exec.done _⟩

theorem Runs.seq (h1 : Runs O p r r' T) (h2 : Runs O q r' r'' T') :
    Runs O (Prog.seq p q) r r'' (T + T') := by
  intro d
  obtain ⟨n1, hn1, he1⟩ := h1 d
  obtain ⟨n2, hn2, he2⟩ := h2 d
  exact ⟨n1 + n2, by omega, by simpa using Exec.seq he1 he2⟩

/-- Sequencing a query-free run with an arbitrary execution. -/
theorem Runs.seqExec {O : Oracle} {p q : Prog} {r r' : Regs} {T : ℕ} {d : Str} {cfg : Cfg}
    {n2 : ℕ} {qs : List Str} (h : Runs O p r r' T) (h2 : Exec O q ⟨r', d⟩ cfg n2 qs) :
    ∃ n, n ≤ T + n2 ∧ Exec O (Prog.seq p q) ⟨r, d⟩ cfg n qs := by
  obtain ⟨n1, hn1, he1⟩ := h d
  exact ⟨n1 + n2, by omega, by simpa using Exec.seq he1 h2⟩

theorem runs_clear (i : ℕ) (r : Regs) :
    Runs O (Prog.clear i) r (Function.update r i []) 1 :=
  fun d => ⟨1, le_rfl, Exec.clear i ⟨r, d⟩⟩

theorem runs_appendBit (i : ℕ) (b : Bool) (r : Regs) :
    Runs O (Prog.appendBit i b) r (Function.update r i (r i ++ [b])) 1 :=
  fun d => ⟨1, le_rfl, Exec.appendBit i b ⟨r, d⟩⟩

theorem runs_appendReg (i j : ℕ) (r : Regs) :
    Runs O (Prog.appendReg i j) r (Function.update r i (r i ++ r j)) (1 + (r j).length) :=
  fun d => ⟨1 + (r j).length, le_rfl, Exec.appendReg i j ⟨r, d⟩⟩

theorem runs_pop (i : ℕ) (r : Regs) :
    Runs O (Prog.pop i) r (Function.update r i (r i).tail) 1 :=
  fun d => ⟨1, le_rfl, Exec.pop i ⟨r, d⟩⟩

/-- Appending a fixed string to a register. -/
def appendConst (i : ℕ) : Str → Prog
  | [] => Prog.done
  | b :: s => Prog.seq (Prog.appendBit i b) (appendConst i s)

theorem noGuess_appendConst (i : ℕ) (s : Str) : noGuess (appendConst i s) := by
  induction s with
  | nil => trivial
  | cons b s ih => exact ⟨trivial, ih⟩

theorem runs_appendConst (i : ℕ) (s : Str) (r : Regs) :
    Runs O (appendConst i s) r (Function.update r i (r i ++ s)) (s.length + 1) := by
  induction s generalizing r with
  | nil =>
      refine (runs_done r).congr ?_
      simp
  | cons b s ih =>
      have h1 : Runs O (Prog.appendBit i b) r (Function.update r i (r i ++ [b])) 1 :=
        runs_appendBit i b r
      have h2 := ih (r := Function.update r i (r i ++ [b]))
      refine ((h1.seq h2).congr ?_).mono ?_
      · funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_apply, hj]
      · simp
        omega

/-- The loop `while ctr ≠ [] do dst := dst ++ src; ctr := tail ctr`. -/
def repeatLoop (ctr src dst : ℕ) : Prog :=
  Prog.loop ctr (Prog.seq (Prog.appendReg dst src) (Prog.pop ctr))

theorem noGuess_repeatLoop (ctr src dst : ℕ) : noGuess (repeatLoop ctr src dst) :=
  ⟨trivial, trivial⟩

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

theorem step_clear (O : Oracle) (r : Regs) (i : ℕ) :
    ∃ r' : Regs, Runs O (Prog.clear i) r r' 1 ∧ r' i = [] ∧ ∀ j, j ≠ i → r' j = r j := by
  refine ⟨Function.update r i [], runs_clear i r, by simp, fun j hj => ?_⟩
  simp [Function.update_apply, hj]

theorem step_appendBit (O : Oracle) (r : Regs) (i : ℕ) (b : Bool) :
    ∃ r' : Regs, Runs O (Prog.appendBit i b) r r' 1 ∧ r' i = r i ++ [b] ∧
      ∀ j, j ≠ i → r' j = r j := by
  refine ⟨Function.update r i (r i ++ [b]), runs_appendBit i b r, by simp, fun j hj => ?_⟩
  simp [Function.update_apply, hj]

theorem step_appendReg (O : Oracle) (r : Regs) (i j : ℕ) :
    ∃ r' : Regs, Runs O (Prog.appendReg i j) r r' (1 + (r j).length) ∧ r' i = r i ++ r j ∧
      ∀ l, l ≠ i → r' l = r l := by
  refine ⟨Function.update r i (r i ++ r j), runs_appendReg i j r, by simp, fun l hl => ?_⟩
  simp [Function.update_apply, hl]

theorem step_appendConst (O : Oracle) (r : Regs) (i : ℕ) (s : Str) :
    ∃ r' : Regs, Runs O (appendConst i s) r r' (s.length + 1) ∧ r' i = r i ++ s ∧
      ∀ j, j ≠ i → r' j = r j := by
  refine ⟨Function.update r i (r i ++ s), runs_appendConst i s r, by simp, fun j hj => ?_⟩
  simp [Function.update_apply, hj]

theorem step_repeatLoop (O : Oracle) (r : Regs) {ctr src dst : ℕ} (hcs : ctr ≠ src)
    (hcd : ctr ≠ dst) (hsd : src ≠ dst) (a : ℕ) (hsrc : r src = List.replicate a true) :
    ∃ r' : Regs, Runs O (repeatLoop ctr src dst) r r' ((r ctr).length * (3 + a) + 1) ∧
      r' dst = r dst ++ List.replicate ((r ctr).length * a) true ∧ r' ctr = [] ∧
      ∀ j, j ≠ ctr → j ≠ dst → r' j = r j := by
  refine ⟨Function.update (Function.update r dst
      (r dst ++ List.replicate ((r ctr).length * a) true)) ctr [],
    runs_repeatLoop hcs hcd hsd a (r ctr) r rfl hsrc, ?_, by simp, fun j h1 h2 => ?_⟩
  · simp [Function.update_apply, Ne.symm hcd]
  · simp [Function.update_apply, h1, h2]

/-! ### Building a long pad -/

/-- Multiplies the length of register `4` by `|r 0| + 2` (registers `3`, `5` are
scratch). -/
def mulBlock : Prog :=
  Prog.seq (Prog.clear 5)
  (Prog.seq (Prog.appendReg 5 4)
  (Prog.seq (Prog.clear 4)
  (Prog.seq (Prog.clear 3)
  (Prog.seq (Prog.appendReg 3 0)
  (Prog.seq (repeatLoop 3 5 4)
  (Prog.seq (Prog.appendReg 4 5) (Prog.appendReg 4 5)))))))

theorem noGuess_mulBlock : noGuess mulBlock := by
  simp [mulBlock, repeatLoop, noGuess]

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
def padProg : ℕ → Prog
  | 0 => Prog.seq (Prog.clear 4) (Prog.appendBit 4 true)
  | m + 1 => Prog.seq (padProg m) mulBlock

theorem noGuess_padProg (m : ℕ) : noGuess (padProg m) := by
  induction m with
  | zero => exact ⟨trivial, trivial⟩
  | succ m ih => exact ⟨ih, noGuess_mulBlock⟩

/-- A (crude) bound for the cost of `padProg`. -/
def padCost : ℕ → ℕ → ℕ
  | 0, _ => 2
  | m + 1, n => padCost m n + 8 * (n + 1) * ((n + 2) ^ m + 1)

theorem polyBdd_padCost (m : ℕ) : PolyBdd (fun n => padCost m n) := by
  induction m with
  | zero => exact polyBdd_const 2
  | succ m ih =>
      refine polyBdd_add ih ?_
      refine polyBdd_mul (polyBdd_mul (polyBdd_const 8) (polyBdd_shift 1)) ?_
      exact polyBdd_add (polyBdd_pow (polyBdd_shift 2) m) (polyBdd_const 1)

theorem runs_padProg (O : Oracle) (m : ℕ) (r : Regs) :
    ∃ r' : Regs, Runs O (padProg m) r r' (padCost m (r 0).length) ∧
      r' 4 = List.replicate (((r 0).length + 2) ^ m) true ∧
      r' 0 = r 0 ∧ r' 1 = r 1 ∧ r' 2 = r 2 := by
  induction m with
  | zero =>
      obtain ⟨r1, e1, v1, o1⟩ := step_clear O r 4
      obtain ⟨r2, e2, v2, o2⟩ := step_appendBit O r1 4 true
      refine ⟨r2, (e1.seq e2).mono (by simp [padCost]), ?_, ?_, ?_, ?_⟩
      · rw [v2, v1]; simp
      · rw [o2 0 (by decide), o1 0 (by decide)]
      · rw [o2 1 (by decide), o1 1 (by decide)]
      · rw [o2 2 (by decide), o1 2 (by decide)]
  | succ m ih =>
      obtain ⟨r1, e1, v1, u0, u1, u2⟩ := ih
      obtain ⟨r2, e2, v2, w0, w1, w2⟩ :=
        runs_mulBlock O r1 (((r 0).length + 2) ^ m) v1
      refine ⟨r2, (e1.seq e2).mono ?_, ?_, ?_, ?_, ?_⟩
      · rw [u0]
        simp only [padCost]
        have : ((r 0).length + 2) ^ m + 1 ≤ ((r 0).length + 2) ^ m + 1 := le_rfl
        nlinarith [Nat.zero_le (((r 0).length + 2) ^ m)]
      · rw [v2, u0, ← pow_succ']
      · rw [w0, u0]
      · rw [w1, u1]
      · rw [w2, u2]

end CS

import RequestProject.Gadgets

/-!
# The nondeterministic program used for the second oracle

`guessProg` guesses a string `w` of the same length as its input and queries the
oracle about `w`.
-/

namespace CS

open Prog

/-- `while r3 ≠ [] do (guess a bit into r2; pop r3)`. -/
def guessLoop : Prog := Prog.loop 3 (Prog.seq (Prog.guess 2) (Prog.pop 3))

/-- On input `x`: guess a string `w` with `|w| = |x|` and query the oracle about it. -/
def guessProg : Prog :=
  Prog.seq (Prog.clear 3)
  (Prog.seq (Prog.appendReg 3 0)
  (Prog.seq (Prog.clear 2)
  (Prog.seq guessLoop (Prog.query 1 2))))

/-- Running the guessing loop with the certificate `w`. -/
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

theorem exec_guessProg_sound (O : Oracle) (x cert : Str) {cfg : Cfg} {n : ℕ} {qs : List Str}
    (h : Exec O guessProg (initCfg x cert) cfg n qs) (hacc : cfg.regs 1 = [true]) :
    ∃ w : Str, w.length = x.length ∧ O w := by
  obtain ⟨c1, _, _, _, _, h1, hr1, _, _⟩ := h.seq_inv
  obtain ⟨rfl, _, _⟩ := h1.clear_inv
  obtain ⟨c2, _, _, _, _, h2, hr2, _, _⟩ := hr1.seq_inv
  obtain ⟨rfl, _, _⟩ := h2.appendReg_inv
  obtain ⟨c3, _, _, _, _, h3, hr3, _, _⟩ := hr2.seq_inv
  obtain ⟨rfl, _, _⟩ := h3.clear_inv
  obtain ⟨c4, _, _, _, _, hloop, hquery, _, _⟩ := hr3.seq_inv
  set rr : Regs := Function.update
      (Function.update (Function.update (initCfg x cert).regs 3 [])
        3 ((Function.update (initCfg x cert).regs 3 []) 3 ++
           (Function.update (initCfg x cert).regs 3 []) 0)) 2 [] with hrr
  have h33 : rr 3 = x := by simp [hrr, initCfg, Function.update_apply]
  obtain ⟨_, w, hwlen, hw2, hwo⟩ := guessLoop_inv O x rr cert c4 _ _ h33 hloop
  have hc32 : rr 2 = [] := by simp [hrr, initCfg, Function.update_apply]
  have hc31 : rr 1 = [] := by simp [hrr, initCfg, Function.update_apply]
  have hc42 : c4.regs 2 = w := by rw [hw2, hc32]; simp
  have hc41 : c4.regs 1 = [] := by rw [hwo 1 (by decide) (by decide), hc31]
  obtain ⟨b, rfl, hb, _⟩ := hquery.query_inv
  refine ⟨w, hwlen, ?_⟩
  have hbtrue : b = true := by
    by_contra hbf
    have : b = false := by cases b <;> simp_all
    subst this
    simp [Function.update_apply, hc41] at hacc
  subst hbtrue
  have := hb.1 rfl
  rwa [hc42] at this

end CS

import RequestProject.Model

/-!
# Auxiliary facts

A counting lemma (there are `2 ^ n` strings of length `n`) and an enumeration of
all programs.
-/

namespace CS

/-- If a list of strings is shorter than `2 ^ n`, some string of length `n` is
missing from it. -/
theorem exists_fresh (n : ℕ) (Q : List Str) (h : Q.length < 2 ^ n) :
    ∃ w : Str, w.length = n ∧ w ∉ Q := by
  by_contra hc
  push_neg at hc
  have hmem : ∀ v : Fin n → Bool, List.ofFn v ∈ Q.toFinset := by
    intro v
    simp only [List.mem_toFinset]
    exact hc _ (by simp)
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card ≤ Q.toFinset.card :=
    Finset.card_le_card_of_injOn _ (fun v _ => hmem v)
      (fun a _ b _ hab => List.ofFn_injective hab)
  simp [Finset.card_univ] at hcard
  have := Q.toFinset_card_le
  omega

deriving instance Countable for CS.Prog

open Classical in
/-- The programs form a countable set, so they can be enumerated. -/
theorem exists_prog_enum : ∃ f : ℕ → Prog, Function.Surjective f := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (α := Prog)
  refine ⟨fun n => if hx : ∃ p, g p = n then hx.choose else Prog.done, fun p => ?_⟩
  refine ⟨g p, ?_⟩
  have hx : ∃ q, g q = g p := ⟨p, rfl⟩
  simp only
  rw [dif_pos hx]
  exact hg hx.choose_spec

/-- A fixed enumeration of all programs. -/
noncomputable def progOf : ℕ → Prog := exists_prog_enum.choose

theorem progOf_surjective : Function.Surjective progOf := exists_prog_enum.choose_spec

end CS

import Mathlib

/-!
# A model of oracle computation

This file sets up a concrete, self-contained model of *oracle machines*: a small
imperative language over string registers, with an explicit cost (time) measure,
nondeterministic guessing, and oracle queries.  On top of it we define the
relativized classes `PClass O` and `NPClass O`.
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings (given as a predicate, classically). -/
abbrev Oracle := Str → Prop

/-- A language is a set of strings. -/
abbrev Language := Str → Prop

/-- Register file: countably many string registers. -/
abbrev Regs := ℕ → Str

/-- A configuration: the registers together with the remaining nondeterministic
guess bits. -/
structure Cfg where
  regs : Regs
  cert : Str

/-- Programs of the machine model.  Register `0` holds the input, register `1`
holds the output. -/
inductive Prog
  | done
  | seq (p q : Prog)
  | clear (i : ℕ)
  | appendBit (i : ℕ) (b : Bool)
  | appendReg (i j : ℕ)
  | pop (i : ℕ)
  | guess (i : ℕ)
  | query (i j : ℕ)
  | loop (i : ℕ) (body : Prog)
  deriving DecidableEq

namespace Prog

/-- `Exec O p c c' n qs` : running program `p` from configuration `c` under oracle
`O` terminates in configuration `c'`, at cost `n`, having asked the oracle
queries `qs` (in order). -/
inductive Exec (O : Oracle) : Prog → Cfg → Cfg → ℕ → List Str → Prop
  | done (c) : Exec O Prog.done c c 1 []
  | seq {p q c1 c2 c3 n1 n2 qs1 qs2} :
      Exec O p c1 c2 n1 qs1 → Exec O q c2 c3 n2 qs2 →
      Exec O (Prog.seq p q) c1 c3 (n1 + n2) (qs1 ++ qs2)
  | clear (i c) :
      Exec O (Prog.clear i) c ⟨Function.update c.regs i [], c.cert⟩ 1 []
  | appendBit (i b c) :
      Exec O (Prog.appendBit i b) c
        ⟨Function.update c.regs i (c.regs i ++ [b]), c.cert⟩ 1 []
  | appendReg (i j c) :
      Exec O (Prog.appendReg i j) c
        ⟨Function.update c.regs i (c.regs i ++ c.regs j), c.cert⟩
        (1 + (c.regs j).length) []
  | pop (i c) :
      Exec O (Prog.pop i) c ⟨Function.update c.regs i (c.regs i).tail, c.cert⟩ 1 []
  | guess {i c b rest} : c.cert = b :: rest →
      Exec O (Prog.guess i) c
        ⟨Function.update c.regs i (c.regs i ++ [b]), rest⟩ 1 []
  | queryT {i j c} : O (c.regs j) →
      Exec O (Prog.query i j) c
        ⟨Function.update c.regs i (c.regs i ++ [true]), c.cert⟩
        (1 + (c.regs j).length) [c.regs j]
  | queryF {i j c} : ¬ O (c.regs j) →
      Exec O (Prog.query i j) c
        ⟨Function.update c.regs i (c.regs i ++ [false]), c.cert⟩
        (1 + (c.regs j).length) [c.regs j]
  | loopDone {i body c} : c.regs i = [] → Exec O (Prog.loop i body) c c 1 []
  | loopStep {i body c c' c'' n1 n2 qs1 qs2} : c.regs i ≠ [] →
      Exec O body c c' n1 qs1 → Exec O (Prog.loop i body) c' c'' n2 qs2 →
      Exec O (Prog.loop i body) c c'' (1 + n1 + n2) (qs1 ++ qs2)

/-- Deterministic programs: those that never guess. -/
def noGuess : Prog → Prop
  | Prog.guess _ => False
  | Prog.seq p q => noGuess p ∧ noGuess q
  | Prog.loop _ b => noGuess b
  | _ => True

variable {O O' : Oracle} {p : Prog} {c c' : Cfg} {n : ℕ} {qs : List Str}

/-- At most one query is asked per unit of cost. -/
theorem Exec.card_queries (h : Exec O p c c' n qs) : qs.length ≤ n := by
  induction h with
  | seq _ _ ih1 ih2 => simp only [List.length_append]; omega
  | loopStep _ _ _ ih1 ih2 => simp only [List.length_append]; omega
  | _ => simp

/-- Auxiliary: bounding register lengths after an update. -/
theorem update_bound {r : Regs} {i : ℕ} {v : Str} {L M : ℕ} (hc : ∀ j, (r j).length ≤ L)
    (hL : L ≤ M) (hv : v.length ≤ M) : ∀ j, ((Function.update r i v) j).length ≤ M := by
  intro j
  rcases eq_or_ne j i with rfl | h
  · simpa using hv
  · rw [Function.update_of_ne h]; exact (hc j).trans hL

/-- Registers grow by at most one symbol per unit of cost; in particular queried
strings are short. -/
theorem Exec.bound (h : Exec O p c c' n qs) (L : ℕ) (hc : ∀ i, (c.regs i).length ≤ L) :
    (∀ i, (c'.regs i).length ≤ L + n) ∧ ∀ s ∈ qs, s.length ≤ L + n := by
  induction h generalizing L with
  | done c => exact ⟨fun i => le_trans (hc i) (by omega), by simp⟩
  | @seq p q c1 c2 c3 n1 n2 qs1 qs2 h1 h2 ih1 ih2 =>
      obtain ⟨hr1, hq1⟩ := ih1 L hc
      obtain ⟨hr2, hq2⟩ := ih2 (L + n1) hr1
      refine ⟨fun i => le_trans (hr2 i) (by omega), ?_⟩
      intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact le_trans (hq1 s hs) (by omega)
      · exact le_trans (hq2 s hs) (by omega)
  | clear i c =>
      exact ⟨update_bound hc (by omega) (by simp), by simp⟩
  | appendBit i b c =>
      refine ⟨update_bound hc (by omega) ?_, by simp⟩
      have := hc i; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  | appendReg i j c =>
      refine ⟨update_bound hc (by omega) ?_, by simp⟩
      have := hc i; have := hc j
      simp only [List.length_append]; omega
  | pop i c =>
      refine ⟨update_bound hc (by omega) ?_, by simp⟩
      have := hc i
      have h2 : (c.regs i).tail.length ≤ (c.regs i).length := by cases c.regs i <;> simp
      omega
  | @guess i c b rest hcert =>
      refine ⟨update_bound hc (by omega) ?_, by simp⟩
      have := hc i; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  | @queryT i j c hO =>
      refine ⟨update_bound hc (by omega) ?_, ?_⟩
      · have := hc i; simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro s hs
        simp only [List.mem_singleton] at hs
        subst hs
        exact le_trans (hc j) (by omega)
  | @queryF i j c hO =>
      refine ⟨update_bound hc (by omega) ?_, ?_⟩
      · have := hc i; simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro s hs
        simp only [List.mem_singleton] at hs
        subst hs
        exact le_trans (hc j) (by omega)
  | loopDone h => exact ⟨fun i => le_trans (hc i) (by omega), by simp⟩
  | @loopStep i body c c' c'' n1 n2 qs1 qs2 hne h1 h2 ih1 ih2 =>
      obtain ⟨hr1, hq1⟩ := ih1 L hc
      obtain ⟨hr2, hq2⟩ := ih2 (L + n1) hr1
      refine ⟨fun i => le_trans (hr2 i) (by omega), ?_⟩
      intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact le_trans (hq1 s hs) (by omega)
      · exact le_trans (hq2 s hs) (by omega)

/-- The result of a computation only depends on the oracle's answers to the
queries actually asked. -/
theorem Exec.locality (h : Exec O p c c' n qs) (hO : ∀ s ∈ qs, (O s ↔ O' s)) :
    Exec O' p c c' n qs := by
  induction h with
  | done c => exact Exec.done c
  | seq h1 h2 ih1 ih2 =>
      exact Exec.seq (ih1 fun s hs => hO s (List.mem_append_left _ hs))
        (ih2 fun s hs => hO s (List.mem_append_right _ hs))
  | clear i c => exact Exec.clear i c
  | appendBit i b c => exact Exec.appendBit i b c
  | appendReg i j c => exact Exec.appendReg i j c
  | pop i c => exact Exec.pop i c
  | guess hcert => exact Exec.guess hcert
  | @queryT i j c hq => exact Exec.queryT ((hO _ (by simp)).1 hq)
  | @queryF i j c hq => exact Exec.queryF fun hc => hq ((hO _ (by simp)).2 hc)
  | loopDone h => exact Exec.loopDone h
  | loopStep hne h1 h2 ih1 ih2 =>
      exact Exec.loopStep hne (ih1 fun s hs => hO s (List.mem_append_left _ hs))
        (ih2 fun s hs => hO s (List.mem_append_right _ hs))

/-! ### Inversion lemmas -/

theorem Exec.seq_inv {cf : Cfg} (h : Exec O (Prog.seq p q) c cf n qs) :
    ∃ (cm : Cfg) (n1 n2 : ℕ) (qs1 qs2 : List Str), Exec O p c cm n1 qs1 ∧
      Exec O q cm cf n2 qs2 ∧ n = n1 + n2 ∧ qs = qs1 ++ qs2 := by
  cases h with
  | seq h1 h2 => exact ⟨_, _, _, _, _, h1, h2, rfl, rfl⟩

theorem Exec.clear_inv {i : ℕ} {cf : Cfg} (h : Exec O (Prog.clear i) c cf n qs) :
    cf = (⟨Function.update c.regs i [], c.cert⟩ : Cfg) ∧ n = 1 ∧ qs = [] := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem Exec.appendReg_inv {i j : ℕ} {cf : Cfg} (h : Exec O (Prog.appendReg i j) c cf n qs) :
    cf = (⟨Function.update c.regs i (c.regs i ++ c.regs j), c.cert⟩ : Cfg) ∧
      n = 1 + (c.regs j).length ∧ qs = [] := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem Exec.query_inv {i j : ℕ} {cf : Cfg} (h : Exec O (Prog.query i j) c cf n qs) :
    ∃ b : Bool, cf = (⟨Function.update c.regs i (c.regs i ++ [b]), c.cert⟩ : Cfg) ∧
      (b = true ↔ O (c.regs j)) ∧ qs = [c.regs j] := by
  cases h with
  | queryT hO => exact ⟨true, rfl, by simp [hO], rfl⟩
  | queryF hO => exact ⟨false, rfl, by simp [hO], rfl⟩

/-- For a program without `guess`, the certificate plays no role. -/
theorem Exec.cert_irrel (h : Exec O p c c' n qs) :
    noGuess p → ∀ d : Str, Exec O p ⟨c.regs, d⟩ ⟨c'.regs, d⟩ n qs := by
  induction h with
  | done c => intro _ d; exact Exec.done _
  | @seq p q c1 c2 c3 n1 n2 qs1 qs2 h1 h2 ih1 ih2 =>
      intro hp d; exact Exec.seq (ih1 hp.1 d) (ih2 hp.2 d)
  | clear i c => intro _ d; exact Exec.clear i ⟨c.regs, d⟩
  | appendBit i b c => intro _ d; exact Exec.appendBit i b ⟨c.regs, d⟩
  | appendReg i j c => intro _ d; exact Exec.appendReg i j ⟨c.regs, d⟩
  | pop i c => intro _ d; exact Exec.pop i ⟨c.regs, d⟩
  | guess hcert => intro hp d; exact absurd hp not_false
  | @queryT i j c hq => intro _ d; exact Exec.queryT (c := ⟨c.regs, d⟩) hq
  | @queryF i j c hq => intro _ d; exact Exec.queryF (c := ⟨c.regs, d⟩) hq
  | @loopDone i body c hnil => intro _ d; exact Exec.loopDone (c := ⟨c.regs, d⟩) hnil
  | @loopStep i body c c1 c2 n1 n2 qs1 qs2 hne h1 h2 ih1 ih2 =>
      intro hp d; exact Exec.loopStep (c := ⟨c.regs, d⟩) hne (ih1 hp d) (ih2 hp d)

/-- Programs without `guess` are deterministic. -/
theorem Exec.det {c1 : Cfg} {n1 : ℕ} {qs1 : List Str} (h1 : Exec O p c c1 n1 qs1) :
    ∀ (c2 : Cfg) (n2 : ℕ) (qs2 : List Str), Exec O p c c2 n2 qs2 → noGuess p →
      c1 = c2 ∧ n1 = n2 ∧ qs1 = qs2 := by
  induction h1 with
  | done c => intro c2 n2 qs2 h2 _; cases h2; exact ⟨rfl, rfl, rfl⟩
  | @seq p q d1 d2 d3 m1 m2 r1 r2 e1 e2 ih1 ih2 =>
      intro c2 n2 qs2 h2 hp
      cases h2 with
      | @seq _ _ _ mid _ _ _ _ _ f1 f2 =>
          obtain ⟨rfl, rfl, rfl⟩ := ih1 _ _ _ f1 hp.1
          obtain ⟨rfl, rfl, rfl⟩ := ih2 _ _ _ f2 hp.2
          exact ⟨rfl, rfl, rfl⟩
  | clear i c => intro c2 n2 qs2 h2 _; cases h2; exact ⟨rfl, rfl, rfl⟩
  | appendBit i b c => intro c2 n2 qs2 h2 _; cases h2; exact ⟨rfl, rfl, rfl⟩
  | appendReg i j c => intro c2 n2 qs2 h2 _; cases h2; exact ⟨rfl, rfl, rfl⟩
  | pop i c => intro c2 n2 qs2 h2 _; cases h2; exact ⟨rfl, rfl, rfl⟩
  | guess hcert => intro c2 n2 qs2 h2 hp; exact absurd hp not_false
  | @queryT i j c hq =>
      intro c2 n2 qs2 h2 _
      cases h2 with
      | queryT _ => exact ⟨rfl, rfl, rfl⟩
      | queryF hq' => exact absurd hq hq'
  | @queryF i j c hq =>
      intro c2 n2 qs2 h2 _
      cases h2 with
      | queryT hq' => exact absurd hq' hq
      | queryF _ => exact ⟨rfl, rfl, rfl⟩
  | @loopDone i body c hnil =>
      intro c2 n2 qs2 h2 _
      cases h2 with
      | loopDone _ => exact ⟨rfl, rfl, rfl⟩
      | loopStep hne _ _ => exact absurd hnil hne
  | @loopStep i body c d1 d2 m1 m2 r1 r2 hne e1 e2 ih1 ih2 =>
      intro c2 n2 qs2 h2 hp
      cases h2 with
      | loopDone hnil => exact absurd hnil hne
      | @loopStep _ _ _ mid _ _ _ _ _ _ f1 f2 =>
          obtain ⟨rfl, rfl, rfl⟩ := ih1 _ _ _ f1 hp
          obtain ⟨rfl, rfl, rfl⟩ := ih2 _ _ _ f2 hp
          exact ⟨rfl, rfl, rfl⟩

end Prog

/-! ### Polynomial bounds -/

/-- `f` is bounded by a polynomial. -/
def PolyBdd (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

theorem polyBdd_mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : PolyBdd g) : PolyBdd f := by
  obtain ⟨c, k, hc⟩ := hg
  exact ⟨c, k, fun n => (h n).trans (hc n)⟩

theorem polyBdd_const (a : ℕ) : PolyBdd (fun _ => a) := ⟨a, 0, fun n => by simp⟩

theorem polyBdd_add {f g : ℕ → ℕ} (hf : PolyBdd f) (hg : PolyBdd g) :
    PolyBdd (fun n => f n + g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, max k1 k2, fun n => ?_⟩
  have e1 : (n + 1) ^ k1 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e2 : (n + 1) ^ k2 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc f n + g n ≤ c1 * (n + 1) ^ k1 + c2 * (n + 1) ^ k2 := Nat.add_le_add (h1 n) (h2 n)
    _ ≤ c1 * (n + 1) ^ max k1 k2 + c2 * (n + 1) ^ max k1 k2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (c1 + c2) * (n + 1) ^ max k1 k2 := by ring

theorem polyBdd_mul {f g : ℕ → ℕ} (hf : PolyBdd f) (hg : PolyBdd g) :
    PolyBdd (fun n => f n * g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 * c2, k1 + k2, fun n => ?_⟩
  calc f n * g n ≤ (c1 * (n + 1) ^ k1) * (c2 * (n + 1) ^ k2) :=
        Nat.mul_le_mul (h1 n) (h2 n)
    _ = c1 * c2 * (n + 1) ^ (k1 + k2) := by rw [pow_add]; ring

theorem polyBdd_shift (a : ℕ) : PolyBdd (fun n => n + a) :=
  ⟨a + 1, 1, fun n => by simpa using by nlinarith⟩

theorem polyBdd_pow {f : ℕ → ℕ} (hf : PolyBdd f) (m : ℕ) : PolyBdd (fun n => f n ^ m) := by
  induction m with
  | zero => simpa using polyBdd_const 1
  | succ m ih =>
      have := polyBdd_mul ih hf
      refine polyBdd_mono (fun n => ?_) this
      rw [pow_succ]

/-- Every polynomially bounded function is bounded by `(n + 2) ^ m` for some `m`;
this lets us normalise polynomial time bounds. -/
theorem polyBdd_le_pow {f : ℕ → ℕ} (hf : PolyBdd f) : ∃ m, ∀ n, f n ≤ (n + 2) ^ m := by
  obtain ⟨c, k, hc⟩ := hf
  refine ⟨k + c, fun n => ?_⟩
  have h1 : c * (n + 1) ^ k ≤ (n + 2) ^ k * (n + 2) ^ c := by
    have e1 : (n + 1) ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
    have e2 : c ≤ (n + 2) ^ c := by
      calc c ≤ 2 ^ c := le_of_lt (Nat.lt_two_pow_self)
        _ ≤ (n + 2) ^ c := Nat.pow_le_pow_left (by omega) c
    calc c * (n + 1) ^ k ≤ (n + 2) ^ c * (n + 2) ^ k := Nat.mul_le_mul e2 e1
      _ = (n + 2) ^ k * (n + 2) ^ c := by ring
  calc f n ≤ c * (n + 1) ^ k := hc n
    _ ≤ (n + 2) ^ k * (n + 2) ^ c := h1
    _ = (n + 2) ^ (k + c) := by rw [pow_add]

/-- The initial configuration on input `x` with guess string `cert`. -/
def initCfg (x cert : Str) : Cfg := ⟨fun i => if i = 0 then x else [], cert⟩

/-- `p` accepts `x` with guess string `cert` within `T` steps under oracle `O`. -/
def AcceptsWithin (O : Oracle) (p : Prog) (x cert : Str) (T : ℕ) : Prop :=
  ∃ c' n qs, n ≤ T ∧ Prog.Exec O p (initCfg x cert) c' n qs ∧ c'.regs 1 = [true]

/-- `p` halts on `x` with guess string `cert` within `T` steps under oracle `O`. -/
def HaltsWithin (O : Oracle) (p : Prog) (x cert : Str) (T : ℕ) : Prop :=
  ∃ c' n qs, n ≤ T ∧ Prog.Exec O p (initCfg x cert) c' n qs

/-- The class `P^O`: languages decided by a deterministic program which,
*whatever the oracle*, halts within a fixed polynomial number of steps (i.e. the
machine carries a polynomial clock). -/
def PClass (O : Oracle) : Set Language :=
  {L | ∃ (p : Prog) (m : ℕ), Prog.noGuess p ∧
        (∀ (O' : Oracle) (x : Str), HaltsWithin O' p x [] ((x.length + 2) ^ m)) ∧
        (∀ x, L x ↔ AcceptsWithin O p x [] ((x.length + 2) ^ m))}

/-- The class `NP^O`: languages accepted by a nondeterministic program within a
polynomial number of steps. -/
def NPClass (O : Oracle) : Set Language :=
  {L | ∃ (p : Prog) (m : ℕ),
        ∀ x, L x ↔ ∃ cert, AcceptsWithin O p x cert ((x.length + 2) ^ m)}

theorem initCfg_bound (x cert : Str) : ∀ i, ((initCfg x cert).regs i).length ≤ x.length := by
  intro i
  simp only [initCfg]
  split <;> simp

/-- All strings queried during a run on input `x` costing `n` have length at most
`|x| + n`. -/
theorem query_len_bound {O : Oracle} {p : Prog} {x cert : Str} {c' : Cfg} {n : ℕ}
    {qs : List Str} (h : Prog.Exec O p (initCfg x cert) c' n qs) :
    ∀ s ∈ qs, s.length ≤ x.length + n :=
  (h.bound x.length (initCfg_bound x cert)).2

/-- Deterministic polynomial time is contained in nondeterministic polynomial
time. -/
theorem PClass_subset_NPClass (O : Oracle) : PClass O ⊆ NPClass O := by
  rintro L ⟨p, m, hdet, _, hcorrect⟩
  refine ⟨p, m, fun x => ?_⟩
  constructor
  · intro hx; exact ⟨[], (hcorrect x).1 hx⟩
  · rintro ⟨cert, c', n, qs, hn, hexec, hacc⟩
    refine (hcorrect x).2 ⟨⟨c'.regs, []⟩, n, qs, hn, ?_, hacc⟩
    have := hexec.cert_irrel hdet []
    simpa [initCfg] using this

end CS

import RequestProject.Gadgets

/-!
# The deterministic program used for the first oracle

`queryProg i m` builds, on input `x`, the string
`1 ^ ((|x|+2)^m) ++ [false] ++ 1 ^ i ++ [false] ++ x`, asks the oracle about it,
and outputs the answer.
-/

namespace CS

open Prog

/-- The query string: a pad of `t` ones, the index `i` in unary, and the input. -/
def encodeQ (i : ℕ) (x : Str) (t : ℕ) : Str :=
  List.replicate t true ++ [false] ++ List.replicate i true ++ [false] ++ x

theorem encodeQ_length (i : ℕ) (x : Str) (t : ℕ) :
    (encodeQ i x t).length = t + 1 + i + 1 + x.length := by
  simp [encodeQ]
  omega

theorem replicate_true_inj {t t' : ℕ} {r r' : Str}
    (h : List.replicate t true ++ false :: r = List.replicate t' true ++ false :: r') :
    t = t' ∧ r = r' := by
  induction t generalizing t' with
  | zero =>
      cases t' with
      | zero => simpa using h
      | succ t' => simp [List.replicate_succ] at h
  | succ t ih =>
      cases t' with
      | zero => simp [List.replicate_succ] at h
      | succ t' =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨ht, hr⟩ := ih h
          exact ⟨by omega, hr⟩

theorem encodeQ_inj {i i' t t' : ℕ} {x x' : Str} (h : encodeQ i x t = encodeQ i' x' t') :
    i = i' ∧ x = x' ∧ t = t' := by
  simp only [encodeQ, List.append_assoc, List.singleton_append] at h
  obtain ⟨ht, h2⟩ := replicate_true_inj h
  obtain ⟨hi, hx⟩ := replicate_true_inj h2
  exact ⟨hi, hx, ht⟩

/-- `queryProg i m`: build the query string in register `2`, ask the oracle, and
put the answer in the output register `1`. -/
def queryProg (i m : ℕ) : Prog :=
  Prog.seq (padProg m)
  (Prog.seq (Prog.clear 2)
  (Prog.seq (Prog.appendReg 2 4)
  (Prog.seq (Prog.appendBit 2 false)
  (Prog.seq (appendConst 2 (List.replicate i true))
  (Prog.seq (Prog.appendBit 2 false)
  (Prog.seq (Prog.appendReg 2 0) (Prog.query 1 2)))))))

theorem noGuess_queryProg (i m : ℕ) : noGuess (queryProg i m) := by
  refine ⟨noGuess_padProg m, trivial, trivial, trivial, ?_, trivial, trivial, trivial⟩
  exact noGuess_appendConst 2 (List.replicate i true)

/-- The exact cost of `queryProg i m` on inputs of length `n`. -/
def qCost (i m n : ℕ) : ℕ := padCost m n + 2 * (n + 2) ^ m + 2 * i + 2 * n + 10

theorem polyBdd_qCost (i m : ℕ) : PolyBdd (fun n => qCost i m n) := by
  refine polyBdd_add (polyBdd_add (polyBdd_add (polyBdd_add (polyBdd_padCost m) ?_)
    (polyBdd_const (2 * i))) ?_) (polyBdd_const 10)
  · exact polyBdd_mul (polyBdd_const 2) (polyBdd_pow (polyBdd_shift 2) m)
  · exact polyBdd_mul (polyBdd_const 2) (polyBdd_mono (fun n => le_rfl) (polyBdd_shift 0))

/-- Behaviour of `queryProg`. -/
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

