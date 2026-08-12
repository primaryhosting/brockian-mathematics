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

import RequestProject.BGS.OracleA
import RequestProject.BGS.OracleB

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Statement: There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header block above is placed directly after the `import` lines, because Lean 4
requires `import` commands to be the very first commands of a module.)

## Summary of the development

Everything is developed from scratch in this project:

* `CS.Stmt`, `CS.step`, `CS.run` (`RequestProject/BGS/Model.lean`): a concrete model of
  oracle computation.  Programs are statements of a small imperative language with
  string registers; oracle queries are built one symbol at a time in a dedicated query
  register, so that *the length of a query never exceeds the number of steps performed*.
* `CS.PClass`, `CS.NPClass` (`RequestProject/BGS/Classes.lean`): the relativized classes
  `P^O` and `NP^O`, defined with the polynomial bounds `pb k n = (n+2)^(k+1)`.
* `CS.A` (`RequestProject/BGS/OracleA.lean`): a self-referential oracle answering
  `NP^A`-questions in one query; well defined by recursion on the length of the queried
  string.  It satisfies `P^A = NP^A`.
* `CS.B` (`RequestProject/BGS/OracleB.lean`): an oracle built by stages, diagonalizing
  against every polynomial time oracle machine, for which the language
  `CS.Lang B = { x | ∃ u, |u| = |x| ∧ u ∈ B }` lies in `NP^B` but not in `P^B`.
-/

namespace CS

/-- **Baker–Gill–Solovay**: there is an oracle `A` with `P^A = NP^A` and an oracle `B`
with `P^B ≠ NP^B`; hence no relativizing proof can settle the `P` versus `NP` question. -/
theorem baker_gill_solovay :
    (∃ A : Oracle, PClass A = NPClass A) ∧ (∃ B : Oracle, PClass B ≠ NPClass B) :=
  ⟨⟨A, PClass_eq_NPClass_A⟩, ⟨B, PClass_ne_NPClass_B⟩⟩

end CS

import RequestProject.BGS.Programs

/-!
# The collapsing oracle `A`

`A` answers, in one step, exactly the questions that a nondeterministic polynomial time
machine (with oracle `A` itself) could ask: a string of the form `0^j 1 0^m 1 x`, where
`j` codes a program `M` together with a degree `k`, belongs to `A` iff `M` accepts `x`
with some short witness, *provided the string is long enough*.  Since queries made during
a `t`-step computation have length at most `t`, the requirement that the string be longer
than the simulated time bound makes this definition well founded by recursion on the
length of the string.
-/

namespace CS

/-- One unfolding of the definition of `A`, relative to an oracle `O` used to answer the
queries of the simulated computations. -/
noncomputable def Astep (O : Oracle) (s : Str) : Bool :=
  match decodeQ s with
  | none => false
  | some p =>
      let k := (Nat.unpair p.1).2
      let M := progOfNat (Nat.unpair p.1).1
      if pb k (p.2.length + pb k p.2.length) < s.length then
        @decide (∃ w : Str, w.length ≤ pb k p.2.length ∧
            Acc M O p.2 w (pb k (p.2.length + w.length))) (Classical.propDecidable _)
      else false

/-- `Astep O s` only depends on the values of `O` on strings shorter than `s`. -/
theorem Astep_congr {O₁ O₂ : Oracle} (s : Str)
    (h : ∀ t : Str, t.length < s.length → O₁ t = O₂ t) : Astep O₁ s = Astep O₂ s := by
  unfold Astep
  cases hd : decodeQ s with
  | none => rfl
  | some p =>
    simp only
    set k := (Nat.unpair p.1).2 with hk
    set M := progOfNat (Nat.unpair p.1).1 with hM
    set x := p.2 with hx
    by_cases hg : pb k (x.length + pb k x.length) < s.length
    · simp only [hg, if_true]
      refine decide_eq_decide.mpr ?_
      have hagree : ∀ u : Str, u.length ≤ pb k (x.length + pb k x.length) → O₁ u = O₂ u := by
        intro u hu
        exact h u (by omega)
      have key : ∀ w : Str, w.length ≤ pb k x.length →
          (Acc M O₁ x w (pb k (x.length + w.length)) ↔ Acc M O₂ x w (pb k (x.length + w.length))) := by
        intro w hw
        have hT : pb k (x.length + w.length) ≤ pb k (x.length + pb k x.length) :=
          pb_mono_right (by omega)
        have hrun := run_congr_of_le O₁ O₂ (pb k (x.length + pb k x.length)) hagree
          (pb k (x.length + w.length)) ([M], initSt x w) (by simpa using hT)
        unfold Acc
        rw [hrun]
      constructor
      · rintro ⟨w, hw, hacc⟩
        exact ⟨w, hw, (key w hw).mp hacc⟩
      · rintro ⟨w, hw, hacc⟩
        exact ⟨w, hw, (key w hw).mpr hacc⟩
    · simp [hg]

/-- `Aupto n` decides `A` correctly on all strings of length `< n`. -/
noncomputable def Aupto : ℕ → Oracle
  | 0 => fun _ => false
  | (n + 1) => fun s => if s.length ≤ n then Astep (Aupto n) s else false

/-- The collapsing oracle. -/
noncomputable def A : Oracle := fun s => Aupto (s.length + 1) s

theorem A_eq_Astep_Aupto (s : Str) : A s = Astep (Aupto s.length) s := by
  show (if s.length ≤ s.length then Astep (Aupto s.length) s else false) = _
  simp

theorem Aupto_eq_A : ∀ (n : ℕ) (s : Str), s.length < n → Aupto n s = A s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro s hs
    cases n with
    | zero => omega
    | succ m =>
      have h1 : Aupto (m + 1) s = Astep (Aupto m) s := by
        show (if s.length ≤ m then Astep (Aupto m) s else false) = _
        simp [Nat.lt_succ_iff.mp hs]
      rw [h1, A_eq_Astep_Aupto]
      refine Astep_congr s ?_
      intro t ht
      have e1 : Aupto m t = A t := IH m (by omega) t (by omega)
      have e2 : Aupto s.length t = A t := IH s.length (by omega) t ht
      rw [e1, e2]

/-- The fixed point equation for `A`. -/
theorem A_eq_Astep (s : Str) : A s = Astep A s := by
  rw [A_eq_Astep_Aupto]
  refine Astep_congr s ?_
  intro t ht
  exact Aupto_eq_A s.length t ht

/-- The defining property of `A` on well formed, long enough query strings. -/
theorem A_encodeQ (M : Stmt) (k : ℕ) (x : Str) (m : ℕ)
    (hlong : pb k (x.length + pb k x.length)
      < (Nat.pair (natOfProg M) k) + m + 2 + x.length) :
    (A (encodeQ (Nat.pair (natOfProg M) k) m x) = true) ↔
      ∃ w : Str, w.length ≤ pb k x.length ∧ Acc M A x w (pb k (x.length + w.length)) := by
  set s := encodeQ (Nat.pair (natOfProg M) k) m x with hs
  have hlen : s.length = (Nat.pair (natOfProg M) k) + m + 2 + x.length := by
    rw [hs, length_encodeQ]
  rw [A_eq_Astep]
  unfold Astep
  rw [show decodeQ s = some (Nat.pair (natOfProg M) k, x) by rw [hs]; exact decodeQ_encodeQ _ _ _]
  simp only [Nat.unpair_pair, progOfNat_natOfProg]
  rw [if_pos (by rw [hlen]; exact hlong)]
  simp

/-! ### `NP^A ⊆ P^A` -/

theorem le_pow_base_two (n c : ℕ) : c ≤ (n + 2) ^ c := by
  calc c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ (n + 2) ^ c := Nat.pow_le_pow_left (by omega) c

/-- The padding written by `simProg j ((k+3)*(k+1))` is long enough for the guard in the
definition of `A`. -/
theorem pad_big (j k : ℕ) (x : Str) :
    pb k (x.length + pb k x.length)
      < j + (x.length + 2) ^ ((k + 3) * (k + 1)) + 2 + x.length := by
  set n := x.length with hn
  have hsq : (4:ℕ) ≤ (n + 2) ^ 2 := by nlinarith
  have hself : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have hpbn : pb k n = (n + 2) ^ (k + 1) := rfl
  have h1 : n + pb k n + 2 ≤ (n + 2) ^ (k + 3) := by
    calc n + pb k n + 2 = (n + 2) + (n + 2) ^ (k + 1) := by rw [hpbn]; ring
      _ ≤ (n + 2) ^ (k + 1) + (n + 2) ^ (k + 1) := by omega
      _ = (n + 2) ^ (k + 1) * 2 := by ring
      _ ≤ (n + 2) ^ (k + 1) * (n + 2) ^ 2 := Nat.mul_le_mul_left _ (by omega)
      _ = (n + 2) ^ (k + 3) := by ring
  have h2 : pb k (n + pb k n) ≤ (n + 2) ^ ((k + 3) * (k + 1)) := by
    show (n + pb k n + 2) ^ (k + 1) ≤ _
    calc (n + pb k n + 2) ^ (k + 1) ≤ ((n + 2) ^ (k + 3)) ^ (k + 1) :=
          Nat.pow_le_pow_left h1 _
      _ = (n + 2) ^ ((k + 3) * (k + 1)) := by rw [← pow_mul]
  omega

/-- The running time of `simProg j d` is polynomially bounded. -/
theorem bound_aux (j d : ℕ) (x : Str) :
    2 * j + 4 * x.length + 18 + (x.length + 2 + 4) ^ (d + 1)
      ≤ pb (2 * j + 3 * d + 21 + 1) x.length := by
  set n := x.length with hn
  set S := 2 * j + 3 * d + 21 with hS
  have hL2 : 2 ≤ n + 2 := by omega
  have hsq : (4:ℕ) ≤ (n + 2) ^ 2 := by nlinarith
  have hcube : (n + 2) ^ 3 = (n + 2) ^ 2 * (n + 2) := by ring
  have e1 : 2 * j ≤ (n + 2) ^ S :=
    le_trans (le_pow_base_two n (2 * j)) (Nat.pow_le_pow_right (by omega) (by omega))
  have e2 : 4 * n ≤ (n + 2) ^ S := by
    have h3 : 4 * n ≤ (n + 2) ^ 3 := by
      rw [hcube]; nlinarith
    exact le_trans h3 (Nat.pow_le_pow_right (by omega) (by omega))
  have e3 : 18 ≤ (n + 2) ^ S :=
    le_trans (le_pow_base_two n 18) (Nat.pow_le_pow_right (by omega) (by omega))
  have e4 : (n + 2 + 4) ^ (d + 1) ≤ (n + 2) ^ S := by
    have hbase : n + 2 + 4 ≤ (n + 2) ^ 3 := by rw [hcube]; nlinarith
    calc (n + 2 + 4) ^ (d + 1) ≤ ((n + 2) ^ 3) ^ (d + 1) := Nat.pow_le_pow_left hbase _
      _ = (n + 2) ^ (3 * (d + 1)) := by rw [← pow_mul]
      _ ≤ (n + 2) ^ S := Nat.pow_le_pow_right (by omega) (by omega)
  have hfinal : 4 * (n + 2) ^ S ≤ pb (S + 1) n := by
    show 4 * (n + 2) ^ S ≤ (n + 2) ^ (S + 1 + 1)
    calc 4 * (n + 2) ^ S ≤ (n + 2) ^ 2 * (n + 2) ^ S := Nat.mul_le_mul_right _ hsq
      _ = (n + 2) ^ (S + 2) := by ring
      _ = (n + 2) ^ (S + 1 + 1) := by ring_nf
  omega

theorem NPClass_subset_PClass : NPClass A ⊆ PClass A := by
  rintro L ⟨M, k, hhalt, hacc⟩
  classical
  refine ⟨simProg (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)),
    2 * (Nat.pair (natOfProg M) k) + 3 * ((k + 3) * (k + 1)) + 21 + 1, ?_, ?_⟩
  · -- the simulating machine halts within the required time bound
    intro x
    obtain ⟨c, st', hc, hex, -⟩ :=
      simProg_exec A (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)) x
    have hb := le_trans hc (bound_aux (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)) x)
    unfold Halts
    rw [hex.run_of_le hb]
  · intro x
    obtain ⟨c, st', hc, hex, hout⟩ :=
      simProg_exec A (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)) x
    have hb := le_trans hc (bound_aux (Nat.pair (natOfProg M) k) ((k + 3) * (k + 1)) x)
    have hrun := hex.run_of_le hb
    have hpad := pad_big (Nat.pair (natOfProg M) k) k x
    rw [hacc x]
    constructor
    · intro hexists
      have hA : A (encodeQ (Nat.pair (natOfProg M) k) ((x.length + 2) ^ ((k + 3) * (k + 1))) x)
          = true := (A_encodeQ M k x _ hpad).mpr hexists
      unfold Acc
      rw [hrun]
      refine ⟨rfl, ?_⟩
      show st'.regs 2 ≠ []
      rw [hout, if_pos hA]
      simp
    · intro hAcc
      have h2 := hAcc.2
      rw [hrun] at h2
      have h3 : st'.regs 2 ≠ [] := h2
      rw [hout] at h3
      by_cases hA : A (encodeQ (Nat.pair (natOfProg M) k)
          ((x.length + 2) ^ ((k + 3) * (k + 1))) x) = true
      · exact (A_encodeQ M k x _ hpad).mp hA
      · simp [hA] at h3

/-- **Relativized collapse**: for the oracle `A`, `P^A = NP^A`. -/
theorem PClass_eq_NPClass_A : PClass A = NPClass A :=
  Set.Subset.antisymm (PClass_subset_NPClass A) NPClass_subset_PClass

end CS

import RequestProject.BGS.Encoding

/-!
# Some concrete programs and their cost analysis

* `pushConstStr l` appends the constant string `l` to the query register;
* `copyToQ i` appends the contents of register `i` to the query register;
* `padProg d` appends `L ^ d` zeros to the query register, where `L` is the length of
  register 9 (used as a "unit" counter).
-/

namespace CS

@[simp] theorem initSt_regs_zero (x w : Str) : (initSt x w).regs 0 = x := rfl
@[simp] theorem initSt_regs_one (x w : Str) : (initSt x w).regs 1 = w := rfl
theorem initSt_regs_other (x w : Str) (i : ℕ) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (initSt x w).regs i = [] := by simp [initSt, h0, h1]

/-- Append the constant string `l` to the query register. -/
def pushConstStr : Str → Stmt
  | [] => Stmt.skip
  | b :: r => Stmt.seq (Stmt.pushQC b) (pushConstStr r)

theorem pushConstStr_exec (O : Oracle) : ∀ (l : Str) (st : St),
    Exec O (pushConstStr l) st { st with q := st.q ++ l } (2 * l.length + 1) := by
  intro l
  induction l with
  | nil => intro st; simpa using Exec.skip O st
  | cons b r ih =>
    intro st
    have h1 := Exec.pushQC O st b
    have h2 := ih { st with q := st.q ++ [b] }
    have := Exec.seq h1 h2
    simp only [List.length_cons] at *
    have heq : ({ st with q := st.q ++ [b] } : St).q ++ r = st.q ++ (b :: r) := by
      simp
    rw [heq] at this
    convert this using 2
    omega

/-- Append the contents of register `i` to the query register, emptying register `i`. -/
def copyToQ (i : ℕ) : Stmt := Stmt.whileNE i (Stmt.seq (Stmt.pushQ i) (Stmt.pop i))

theorem copyToQ_exec (O : Oracle) (i : ℕ) : ∀ (v : Str) (st : St), st.regs i = v →
    Exec O (copyToQ i) st
      { st with regs := Function.update st.regs i [], q := st.q ++ v } (4 * v.length + 1) := by
  intro v
  induction v with
  | nil =>
    intro st hst
    have h : ({ st with regs := Function.update st.regs i [], q := st.q ++ [] } : St) = st := by
      have : Function.update st.regs i [] = st.regs := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [hst]
        · simp [Function.update_of_ne hj]
      simp [this]
    rw [h]
    simpa using Exec.while_done (O := O) (body := Stmt.seq (Stmt.pushQ i) (Stmt.pop i)) (by rw [hst])
  | cons b r ih =>
    intro st hst
    have hne : st.regs i ≠ [] := by rw [hst]; simp
    -- body
    have h1 : Exec O (Stmt.pushQ i) st { st with q := st.q ++ [b] } 1 := by
      have := Exec.pushQ O st i
      rwa [hst] at this
    have h2 := Exec.pop O { st with q := st.q ++ [b] } i
    have hbody := Exec.seq h1 h2
    set st1 : St := (({ st with q := st.q ++ [b] } : St).setReg i
      ((({ st with q := st.q ++ [b] } : St)).regs i).tail) with hst1
    have hst1r : st1.regs i = r := by
      simp [hst1, St.setReg, hst]
    have hih := ih st1 hst1r
    have hres : ({ st1 with regs := Function.update st1.regs i [], q := st1.q ++ r } : St)
        = { st with regs := Function.update st.regs i [], q := st.q ++ (b :: r) } := by
      have hregs : Function.update st1.regs i [] = Function.update st.regs i [] := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hst1, St.setReg, Function.update_of_ne hj]
      have hq : st1.q ++ r = st.q ++ (b :: r) := by
        simp [hst1, St.setReg]
      simp only [hst1] at *
      exact St.mk.injEq .. ▸ ⟨hregs, hq, rfl⟩
    rw [hres] at hih
    have := Exec.while_step hne hbody hih
    convert this using 2
    simp
    omega

/-- `padProg d` appends `L ^ d` zeros to the query register, where `L` is the length of
register 9.  Registers `10, …, 9 + d` are used as loop counters. -/
def padProg : ℕ → Stmt
  | 0 => Stmt.pushQC false
  | (d + 1) => Stmt.seq (Stmt.copy (10 + d) 9)
      (Stmt.whileNE (10 + d) (Stmt.seq (padProg d) (Stmt.pop (10 + d))))

theorem padProg_exec (O : Oracle) : ∀ (d : ℕ) (st : St),
    ∃ (c : ℕ) (st' : St), c ≤ ((st.regs 9).length + 4) ^ (d + 1) ∧ Exec O (padProg d) st st' c ∧
      st'.q = st.q ++ List.replicate ((st.regs 9).length ^ d) false ∧
      (∀ j, (j ≤ 9 ∨ 10 + d ≤ j) → st'.regs j = st.regs j) ∧ st'.log = st.log := by
  intro d
  induction d with
  | zero =>
    intro st
    refine ⟨1, { st with q := st.q ++ [false] }, ?_, Exec.pushQC O st false, ?_, ?_, rfl⟩
    · simp
    · simp
    · intro j _; rfl
  | succ d IH =>
    have loop : ∀ (ℓ : ℕ) (st : St), (st.regs (10 + d)).length = ℓ →
        ∃ (c : ℕ) (st' : St),
          c ≤ ℓ * (((st.regs 9).length + 4) ^ (d + 1) + 3) + 1 ∧
          Exec O (Stmt.whileNE (10 + d) (Stmt.seq (padProg d) (Stmt.pop (10 + d)))) st st' c ∧
          st'.q = st.q ++ List.replicate (ℓ * (st.regs 9).length ^ d) false ∧
          (∀ j, (j ≤ 9 ∨ 11 + d ≤ j) → st'.regs j = st.regs j) ∧ st'.log = st.log := by
      intro ℓ
      induction ℓ with
      | zero =>
        intro st h
        refine ⟨1, st, by omega, Exec.while_done (by simpa using h), by simp, ?_, rfl⟩
        intro j _; rfl
      | succ ℓ ihl =>
        intro st h
        have hne : st.regs (10 + d) ≠ [] := by
          intro hc; rw [hc] at h; simp at h
        obtain ⟨c₁, st₁, hc₁, hex₁, hq₁, hr₁, hl₁⟩ := IH st
        have h9 : st₁.regs 9 = st.regs 9 := hr₁ 9 (Or.inl (by omega))
        have hcnt : st₁.regs (10 + d) = st.regs (10 + d) := hr₁ (10 + d) (Or.inr (by omega))
        have hpop := Exec.pop O st₁ (10 + d)
        set st₂ : St := st₁.setReg (10 + d) (st₁.regs (10 + d)).tail with hst₂
        have hbody := Exec.seq hex₁ hpop
        have h9' : st₂.regs 9 = st.regs 9 := by
          rw [hst₂, St.setReg_ne _ (by omega), h9]
        have hcnt' : (st₂.regs (10 + d)).length = ℓ := by
          rw [hst₂, St.setReg_same, hcnt]
          rcases hx : st.regs (10 + d) with _ | ⟨a, r⟩
          · rw [hx] at h; simp at h
          · rw [hx] at h; simp at h ⊢; omega
        obtain ⟨c₂, st₃, hc₂, hex₂, hq₂, hr₂, hl₂⟩ := ihl st₂ hcnt'
        refine ⟨c₁ + 1 + 1 + c₂ + 1, st₃, ?_, Exec.while_step hne hbody hex₂, ?_, ?_, ?_⟩
        · rw [h9'] at hc₂
          have h1 : (ℓ + 1) * (((st.regs 9).length + 4) ^ (d + 1) + 3) + 1
              = ℓ * (((st.regs 9).length + 4) ^ (d + 1) + 3)
                + ((st.regs 9).length + 4) ^ (d + 1) + 4 := by ring
          rw [h1]
          linarith [hc₁, hc₂]
        · have hq3 : st₃.q = st.q ++ (List.replicate ((st.regs 9).length ^ d) false
              ++ List.replicate (ℓ * (st.regs 9).length ^ d) false) := by
            rw [hq₂, h9', hst₂]
            show st₁.q ++ _ = _
            rw [hq₁, List.append_assoc]
          have harith : (st.regs 9).length ^ d + ℓ * (st.regs 9).length ^ d
              = (ℓ + 1) * (st.regs 9).length ^ d := by ring
          rw [hq3, ← List.replicate_add, harith]
        · intro j hj
          rw [hr₂ j hj, hst₂, St.setReg_ne _ (by omega), hr₁ j (by omega)]
        · rw [hl₂, hst₂]
          show st₁.log = st.log
          exact hl₁
    intro st
    have hcopy := Exec.copy O st (10 + d) 9
    set st₀ : St := st.setReg (10 + d) (st.regs 9) with hst₀
    have h9 : st₀.regs 9 = st.regs 9 := by rw [hst₀, St.setReg_ne _ (by omega)]
    have hcnt : (st₀.regs (10 + d)).length = (st.regs 9).length := by
      rw [hst₀, St.setReg_same]
    obtain ⟨c, st', hc, hex, hq, hr, hl⟩ := loop ((st.regs 9).length) st₀ hcnt
    rw [h9] at hc hq
    refine ⟨1 + c + 1, st', ?_, Exec.seq hcopy hex, ?_, ?_, ?_⟩
    · set L := (st.regs 9).length
      set X := (L + 4) ^ (d + 1) with hX
      have hXge : L + 4 ≤ X := by
        rw [hX]
        calc L + 4 = (L + 4) ^ 1 := (pow_one _).symm
          _ ≤ (L + 4) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hpow : ((L + 4) ^ (d + 1 + 1)) = (L + 4) * X := by
        rw [hX]; ring
      rw [hpow]
      have key : L * (X + 3) + 1 + 2 ≤ (L + 4) * X := by nlinarith
      linarith [hc]
    · rw [hq, hst₀]
      show st.q ++ _ = _
      congr 2
      rw [← pow_succ']
    · intro j hj
      rw [hr j (by omega), hst₀, St.setReg_ne _ (by omega)]
    · rw [hl, hst₀]
      rfl

/-- A sanity check on the model: the language of nonempty strings is decided in
polynomial time relative to every oracle. -/
theorem nonempty_mem_PClass (O : Oracle) : (fun x : Str => decide (x ≠ [])) ∈ PClass O := by
  have key : ∀ x : Str, ∃ st' : St,
      Exec O (Stmt.ifNE 0 (Stmt.pushC 2 true) Stmt.skip) (initSt x []) st' 2 ∧
        (st'.regs 2 ≠ [] ↔ x ≠ []) := by
    intro x
    by_cases hx : x = []
    · refine ⟨initSt x [], Exec.ifNE_neg (by simp [hx]) (Exec.skip O _), ?_⟩
      simp [hx, initSt_regs_other]
    · refine ⟨(initSt x []).setReg 2 (true :: (initSt x []).regs 2),
        Exec.ifNE_pos (by simpa using hx) (Exec.pushC O _ 2 true), ?_⟩
      simp [hx]
  refine ⟨Stmt.ifNE 0 (Stmt.pushC 2 true) Stmt.skip, 0, ?_, ?_⟩
  · intro x
    obtain ⟨st', hex, -⟩ := key x
    unfold Halts
    rw [hex.run_of_le (two_le_pb 0 x.length)]
  · intro x
    obtain ⟨st', hex, hiff⟩ := key x
    unfold Acc
    rw [hex.run_of_le (two_le_pb 0 x.length)]
    simp [hiff]

/-- The program which, on input `x`, writes the query string `0^j 1 0^m 1 x` (with
`m = (|x|+2)^d`) into the query register and asks the oracle about it, storing the answer
in the output register 2. -/
def simProg (j d : ℕ) : Stmt :=
  Stmt.seq (Stmt.copy 9 0)
  (Stmt.seq (Stmt.pushC 9 false)
  (Stmt.seq (Stmt.pushC 9 false)
  (Stmt.seq (pushConstStr (List.replicate j false))
  (Stmt.seq (Stmt.pushQC true)
  (Stmt.seq (padProg d)
  (Stmt.seq (Stmt.pushQC true)
  (Stmt.seq (Stmt.copy 8 0)
  (Stmt.seq (copyToQ 8) (Stmt.query 2)))))))))

theorem simProg_exec (O : Oracle) (j d : ℕ) (x : Str) :
    ∃ (c : ℕ) (st' : St),
      c ≤ 2 * j + 4 * x.length + 18 + (x.length + 2 + 4) ^ (d + 1) ∧
      Exec O (simProg j d) (initSt x []) st' c ∧
      st'.regs 2 = (if O (encodeQ j ((x.length + 2) ^ d) x) then [true] else []) := by
  set n := x.length with hn
  -- step 1 : `regs 9 := x`
  have e1 := Exec.copy O (initSt x []) 9 0
  set s1 : St := (initSt x []).setReg 9 ((initSt x []).regs 0) with hs1
  have hs1q : s1.q = [] := rfl
  have hs1r0 : s1.regs 0 = x := by rw [hs1, St.setReg_ne _ (by omega)]; simp
  have hs1r9 : s1.regs 9 = x := by rw [hs1, St.setReg_same]; simp
  -- steps 2 and 3 : two zeros in front of register 9
  have e2 := Exec.pushC O s1 9 false
  set s2 : St := s1.setReg 9 (false :: s1.regs 9) with hs2
  have hs2q : s2.q = [] := hs1q
  have hs2r0 : s2.regs 0 = x := by rw [hs2, St.setReg_ne _ (by omega)]; exact hs1r0
  have hs2r9 : s2.regs 9 = false :: x := by rw [hs2, St.setReg_same, hs1r9]
  have e3 := Exec.pushC O s2 9 false
  set s3 : St := s2.setReg 9 (false :: s2.regs 9) with hs3
  have hs3q : s3.q = [] := hs2q
  have hs3r0 : s3.regs 0 = x := by rw [hs3, St.setReg_ne _ (by omega)]; exact hs2r0
  have hs3r9 : s3.regs 9 = false :: false :: x := by rw [hs3, St.setReg_same, hs2r9]
  -- step 4 : the constant prefix `0^j`
  have e4 := pushConstStr_exec O (List.replicate j false) s3
  set s4 : St := { s3 with q := s3.q ++ List.replicate j false } with hs4
  have hs4q : s4.q = List.replicate j false := by rw [hs4]; show s3.q ++ _ = _; rw [hs3q]; simp
  have hs4r0 : s4.regs 0 = x := hs3r0
  have hs4r9 : s4.regs 9 = false :: false :: x := hs3r9
  -- step 5 : the separator
  have e5 := Exec.pushQC O s4 true
  set s5 : St := { s4 with q := s4.q ++ [true] } with hs5
  have hs5q : s5.q = List.replicate j false ++ [true] := by
    rw [hs5]; show s4.q ++ _ = _; rw [hs4q]
  have hs5r0 : s5.regs 0 = x := hs4r0
  have hs5r9 : s5.regs 9 = false :: false :: x := hs4r9
  have hs5len : (s5.regs 9).length = n + 2 := by rw [hs5r9]; simp [hn]
  -- step 6 : the padding
  obtain ⟨c6, s6, hc6, e6, hq6, hr6, -⟩ := padProg_exec O d s5
  rw [hs5len] at hc6 hq6
  have hs6r0 : s6.regs 0 = x := by rw [hr6 0 (by omega)]; exact hs5r0
  have hs6q : s6.q = List.replicate j false ++ [true] ++ List.replicate ((n + 2) ^ d) false := by
    rw [hq6, hs5q]
  -- step 7 : the second separator
  have e7 := Exec.pushQC O s6 true
  set s7 : St := { s6 with q := s6.q ++ [true] } with hs7
  have hs7q : s7.q
      = List.replicate j false ++ [true] ++ List.replicate ((n + 2) ^ d) false ++ [true] := by
    rw [hs7]; show s6.q ++ _ = _; rw [hs6q]
  have hs7r0 : s7.regs 0 = x := hs6r0
  -- step 8 : copy the input into a scratch register
  have e8 := Exec.copy O s7 8 0
  set s8 : St := s7.setReg 8 (s7.regs 0) with hs8
  have hs8r8 : s8.regs 8 = x := by rw [hs8, St.setReg_same, hs7r0]
  have hs8q : s8.q
      = List.replicate j false ++ [true] ++ List.replicate ((n + 2) ^ d) false ++ [true] := hs7q
  -- step 9 : append the input to the query register
  have e9 := copyToQ_exec O 8 x s8 hs8r8
  set s9 : St := { s8 with regs := Function.update s8.regs 8 [], q := s8.q ++ x } with hs9
  have hs9q : s9.q = encodeQ j ((n + 2) ^ d) x := by
    rw [hs9]
    show s8.q ++ x = _
    rw [hs8q]
    simp [encodeQ]
  -- step 10 : the oracle call
  have e10 := Exec.query O s9 2
  refine ⟨_, _, ?_, Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seq e4 (Exec.seq e5
      (Exec.seq e6 (Exec.seq e7 (Exec.seq e8 (Exec.seq e9 e10)))))))), ?_⟩
  · simp only [List.length_replicate, ← hn]
    generalize (n + 2 + 4) ^ (d + 1) = X at hc6 ⊢
    omega
  · show Function.update s9.regs 2 (if O s9.q then [true] else []) 2 = _
    rw [hs9q]
    simp

end CS

import Mathlib

/-!
# A concrete model of oracle computation

Strings are lists of booleans, an oracle is a boolean-valued function on strings.
Machines are programs of a small imperative language with registers holding strings
and a distinguished *query register* `q` which is filled one symbol at a time and is
emptied by each oracle call.  This convention guarantees the fundamental property

  *the length of every oracle query is bounded by the number of steps of the computation*

which is what makes the self-referential oracle of Baker-Gill-Solovay well defined.
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, given by its characteristic function. -/
abbrev Oracle := Str → Bool

/-- Programs. -/
inductive Stmt where
  /-- do nothing -/
  | skip : Stmt
  /-- sequential composition -/
  | seq : Stmt → Stmt → Stmt
  /-- `regs i := b :: regs i` -/
  | pushC : ℕ → Bool → Stmt
  /-- `regs i := (regs i).tail` -/
  | pop : ℕ → Stmt
  /-- `regs i := regs j` -/
  | copy : ℕ → ℕ → Stmt
  /-- append the first symbol of `regs i` to the query register -/
  | pushQ : ℕ → Stmt
  /-- append a constant symbol to the query register -/
  | pushQC : Bool → Stmt
  /-- ask the oracle about the contents of the query register, store the answer in
  `regs i` (as `[true]` or `[]`) and empty the query register -/
  | query : ℕ → Stmt
  /-- `while regs i ≠ [] do body` -/
  | whileNE : ℕ → Stmt → Stmt
  /-- `if regs i ≠ [] then a else b` -/
  | ifNE : ℕ → Stmt → Stmt → Stmt
  deriving Inhabited, DecidableEq

/-- Machine states: registers, the query register, and a log of all queries made. -/
structure St where
  regs : ℕ → Str
  q : Str
  log : List Str

/-- Configurations: a stack of statements still to be executed, and a state. -/
abbrev Cfg := List Stmt × St

/-- One computation step. A configuration with empty statement stack is halted. -/
def step (O : Oracle) : Cfg → Cfg
  | ([], st) => ([], st)
  | (Stmt.skip :: r, st) => (r, st)
  | (Stmt.seq a b :: r, st) => (a :: b :: r, st)
  | (Stmt.pushC i b :: r, st) => (r, { st with regs := Function.update st.regs i (b :: st.regs i) })
  | (Stmt.pop i :: r, st) => (r, { st with regs := Function.update st.regs i (st.regs i).tail })
  | (Stmt.copy i j :: r, st) => (r, { st with regs := Function.update st.regs i (st.regs j) })
  | (Stmt.pushQ i :: r, st) => (r, { st with q := st.q ++ [(st.regs i).headD false] })
  | (Stmt.pushQC b :: r, st) => (r, { st with q := st.q ++ [b] })
  | (Stmt.query i :: r, st) =>
      (r, { regs := Function.update st.regs i (if O st.q then [true] else []),
            q := [], log := st.log ++ [st.q] })
  | (Stmt.whileNE i body :: r, st) =>
      if st.regs i = [] then (r, st) else (body :: Stmt.whileNE i body :: r, st)
  | (Stmt.ifNE i a b :: r, st) => if st.regs i = [] then (b :: r, st) else (a :: r, st)

/-- Running a configuration for `t` steps. -/
def run (O : Oracle) (t : ℕ) (c : Cfg) : Cfg := (step O)^[t] c

@[simp] theorem run_zero (O : Oracle) (c : Cfg) : run O 0 c = c := rfl

theorem run_succ (O : Oracle) (t : ℕ) (c : Cfg) : run O (t + 1) c = run O t (step O c) := by
  simp [run, Function.iterate_succ_apply]

theorem run_succ' (O : Oracle) (t : ℕ) (c : Cfg) : run O (t + 1) c = step O (run O t c) := by
  simp [run, Function.iterate_succ_apply']

theorem run_add (O : Oracle) (t₁ t₂ : ℕ) (c : Cfg) :
    run O (t₁ + t₂) c = run O t₁ (run O t₂ c) := by
  simp [run, Function.iterate_add_apply]

@[simp] theorem step_nil (O : Oracle) (st : St) : step O ([], st) = ([], st) := rfl

@[simp] theorem run_nil (O : Oracle) (t : ℕ) (st : St) : run O t ([], st) = ([], st) := by
  induction t with
  | zero => rfl
  | succ n ih => rw [run_succ, step_nil, ih]

/-- Once halted, always halted, with the same state. -/
theorem run_halted_mono (O : Oracle) {t t' : ℕ} (h : t ≤ t') (c : Cfg)
    (hh : (run O t c).1 = []) : run O t' c = run O t c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, run_add]
  have hcfg : run O t c = ([], (run O t c).2) := by
    rcases hx : run O t c with ⟨l, st⟩
    rw [hx] at hh
    simp only at hh
    simp [hh]
  rw [hcfg, run_nil]

/-! ### Locality: the query register grows by at most one symbol per step -/

theorem q_length_step (O : Oracle) (c : Cfg) : (step O c).2.q.length ≤ c.2.q.length + 1 := by
  obtain ⟨l, st⟩ := c
  match l with
  | [] => simp [step]
  | Stmt.skip :: r => simp [step]
  | Stmt.seq a b :: r => simp [step]
  | Stmt.pushC i b :: r => simp [step]
  | Stmt.pop i :: r => simp [step]
  | Stmt.copy i j :: r => simp [step]
  | Stmt.pushQ i :: r => simp [step]
  | Stmt.pushQC b :: r => simp [step]
  | Stmt.query i :: r => simp [step]
  | Stmt.whileNE i body :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]
  | Stmt.ifNE i a b :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]

/-- If two oracles agree on all strings of length at most `T`, then any computation of at
most `T` steps (started with a short enough query register) cannot distinguish them. -/
theorem run_congr_of_le (O₁ O₂ : Oracle) (T : ℕ) (h : ∀ s : Str, s.length ≤ T → O₁ s = O₂ s) :
    ∀ (t : ℕ) (c : Cfg), c.2.q.length + t ≤ T → run O₁ t c = run O₂ t c := by
  intro t
  induction t with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    have hstep : step O₁ c = step O₂ c := by
      obtain ⟨l, st⟩ := c
      match l with
      | [] => rfl
      | Stmt.skip :: r => rfl
      | Stmt.seq a b :: r => rfl
      | Stmt.pushC i b :: r => rfl
      | Stmt.pop i :: r => rfl
      | Stmt.copy i j :: r => rfl
      | Stmt.pushQ i :: r => rfl
      | Stmt.pushQC b :: r => rfl
      | Stmt.query i :: r =>
          have hq : O₁ st.q = O₂ st.q := by
            refine h st.q ?_
            simp only at hc
            omega
          simp [step, hq]
      | Stmt.whileNE i body :: r => rfl
      | Stmt.ifNE i a b :: r => rfl
    rw [run_succ, run_succ, hstep]
    refine ih _ ?_
    have := q_length_step O₂ c
    omega

/-! ### Locality: only logged queries matter -/

theorem log_prefix_step (O : Oracle) (c : Cfg) : c.2.log <+: (step O c).2.log := by
  obtain ⟨l, st⟩ := c
  match l with
  | [] => simp [step]
  | Stmt.skip :: r => simp [step]
  | Stmt.seq a b :: r => simp [step]
  | Stmt.pushC i b :: r => simp [step]
  | Stmt.pop i :: r => simp [step]
  | Stmt.copy i j :: r => simp [step]
  | Stmt.pushQ i :: r => simp [step]
  | Stmt.pushQC b :: r => simp [step]
  | Stmt.query i :: r => exact ⟨[st.q], rfl⟩
  | Stmt.whileNE i body :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]
  | Stmt.ifNE i a b :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]

theorem log_length_step (O : Oracle) (c : Cfg) :
    (step O c).2.log.length ≤ c.2.log.length + 1 := by
  obtain ⟨l, st⟩ := c
  match l with
  | [] => simp [step]
  | Stmt.skip :: r => simp [step]
  | Stmt.seq a b :: r => simp [step]
  | Stmt.pushC i b :: r => simp [step]
  | Stmt.pop i :: r => simp [step]
  | Stmt.copy i j :: r => simp [step]
  | Stmt.pushQ i :: r => simp [step]
  | Stmt.pushQC b :: r => simp [step]
  | Stmt.query i :: r => simp [step]
  | Stmt.whileNE i body :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]
  | Stmt.ifNE i a b :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]

theorem log_prefix_run (O : Oracle) (t : ℕ) (c : Cfg) : c.2.log <+: (run O t c).2.log := by
  induction t generalizing c with
  | zero => exact List.prefix_rfl
  | succ n ih => rw [run_succ]; exact (log_prefix_step O c).trans (ih (c := step O c))

theorem log_length_run (O : Oracle) (t : ℕ) (c : Cfg) :
    (run O t c).2.log.length ≤ c.2.log.length + t := by
  induction t generalizing c with
  | zero => simp
  | succ n ih =>
    rw [run_succ]
    have h1 := ih (c := step O c)
    have h2 := log_length_step O c
    omega

theorem log_step_cases (O : Oracle) (c : Cfg) :
    (step O c).2.log = c.2.log ∨ (step O c).2.log = c.2.log ++ [c.2.q] := by
  obtain ⟨l, st⟩ := c
  match l with
  | [] => exact Or.inl rfl
  | Stmt.skip :: r => exact Or.inl rfl
  | Stmt.seq a b :: r => exact Or.inl rfl
  | Stmt.pushC i b :: r => exact Or.inl rfl
  | Stmt.pop i :: r => exact Or.inl rfl
  | Stmt.copy i j :: r => exact Or.inl rfl
  | Stmt.pushQ i :: r => exact Or.inl rfl
  | Stmt.pushQC b :: r => exact Or.inl rfl
  | Stmt.query i :: r => exact Or.inr rfl
  | Stmt.whileNE i body :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]
  | Stmt.ifNE i a b :: r =>
      by_cases h : st.regs i = [] <;> simp [step, h]

/-- Every string queried during a run of at most `N` steps has length at most `N`. -/
theorem log_mem_length_le (O : Oracle) (N : ℕ) :
    ∀ (t : ℕ) (c : Cfg), (∀ s ∈ c.2.log, s.length ≤ N) → c.2.q.length + t ≤ N →
      ∀ s ∈ (run O t c).2.log, s.length ≤ N := by
  intro t
  induction t with
  | zero => intro c h _ s hs; exact h s hs
  | succ n ih =>
    intro c h hq s hs
    rw [run_succ] at hs
    refine ih (step O c) ?_ ?_ s hs
    · intro u hu
      rcases log_step_cases O c with hc | hc
      · rw [hc] at hu; exact h u hu
      · rw [hc] at hu
        rcases List.mem_append.mp hu with hu' | hu'
        · exact h u hu'
        · rw [List.mem_singleton.mp hu']
          omega
    · have := q_length_step O c
      omega

/-- If `O₂` agrees with `O₁` on every string queried during a run of `O₁`, the two runs
coincide. -/
theorem run_congr_of_log (O₁ O₂ : Oracle) :
    ∀ (t : ℕ) (c : Cfg), (∀ s ∈ (run O₁ t c).2.log, O₁ s = O₂ s) → run O₂ t c = run O₁ t c := by
  intro t
  induction t with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hc
    rw [run_succ] at hc ⊢
    have hstep : step O₂ c = step O₁ c := by
      obtain ⟨l, st⟩ := c
      match l with
      | [] => rfl
      | Stmt.skip :: r => rfl
      | Stmt.seq a b :: r => rfl
      | Stmt.pushC i b :: r => rfl
      | Stmt.pop i :: r => rfl
      | Stmt.copy i j :: r => rfl
      | Stmt.pushQ i :: r => rfl
      | Stmt.pushQC b :: r => rfl
      | Stmt.query i :: r =>
          have hmem : st.q ∈ (run O₁ n (step O₁ (Stmt.query i :: r, st))).2.log := by
            have hp := log_prefix_run O₁ n (step O₁ (Stmt.query i :: r, st))
            refine hp.subset ?_
            simp [step]
          have hq := hc _ hmem
          simp [step, hq]
      | Stmt.whileNE i body :: r => rfl
      | Stmt.ifNE i a b :: r => rfl
    rw [hstep]
    exact ih _ hc

end CS

import RequestProject.BGS.Classes

/-!
# Encodings

* an enumeration of all programs by natural numbers;
* the format of the strings that are handed to the collapsing oracle `A`:
  `0^j 1 0^m 1 x`, where `j` codes a program together with a polynomial degree,
  `0^m` is padding making the string long, and `x` is the actual input.
-/

namespace CS

deriving instance Countable for Stmt

noncomputable instance : Encodable Stmt := Encodable.ofCountable Stmt

/-- The code of a program. -/
noncomputable def natOfProg (M : Stmt) : ℕ := Encodable.encode M

/-- The program with a given code (garbage programs are `skip`). -/
noncomputable def progOfNat (n : ℕ) : Stmt := (Encodable.decode (α := Stmt) n).getD Stmt.skip

@[simp] theorem progOfNat_natOfProg (M : Stmt) : progOfNat (natOfProg M) = M := by
  simp [progOfNat, natOfProg]

/-! ### The query format -/

/-- Read a block `0^j 1` off the front of a string, returning `j` and the remainder. -/
def splitOnes : Str → Option (ℕ × Str)
  | [] => none
  | true :: r => some (0, r)
  | false :: r => (splitOnes r).map (fun p => (p.1 + 1, p.2))

/-- Decode a query string `0^j 1 0^m 1 x` into the pair `(j, x)`. -/
def decodeQ (s : Str) : Option (ℕ × Str) :=
  match splitOnes s with
  | none => none
  | some p =>
    match splitOnes p.2 with
    | none => none
    | some p2 => some (p.1, p2.2)

/-- The query string `0^j 1 0^m 1 x`. -/
def encodeQ (j m : ℕ) (x : Str) : Str :=
  List.replicate j false ++ true :: (List.replicate m false ++ true :: x)

theorem splitOnes_replicate (j : ℕ) (r : Str) :
    splitOnes (List.replicate j false ++ true :: r) = some (j, r) := by
  induction j with
  | zero => simp [splitOnes]
  | succ n ih => simp [List.replicate_succ, splitOnes, ih]

@[simp] theorem decodeQ_encodeQ (j m : ℕ) (x : Str) : decodeQ (encodeQ j m x) = some (j, x) := by
  unfold decodeQ encodeQ
  rw [splitOnes_replicate]
  simp [splitOnes_replicate]

@[simp] theorem length_encodeQ (j m : ℕ) (x : Str) :
    (encodeQ j m x).length = j + m + 2 + x.length := by
  simp [encodeQ]
  omega

end CS

import RequestProject.BGS.Model

/-!
# Big-step execution with explicit costs

`Exec O a st st' c` says: executing statement `a` from state `st` takes exactly `c` steps
and produces state `st'`, independently of the rest of the statement stack.
-/

namespace CS

/-- Set a register. -/
def St.setReg (st : St) (i : ℕ) (v : Str) : St :=
  { st with regs := Function.update st.regs i v }

@[simp] theorem St.setReg_q (st : St) (i : ℕ) (v : Str) : (st.setReg i v).q = st.q := rfl
@[simp] theorem St.setReg_log (st : St) (i : ℕ) (v : Str) : (st.setReg i v).log = st.log := rfl
@[simp] theorem St.setReg_same (st : St) (i : ℕ) (v : Str) : (st.setReg i v).regs i = v := by
  simp [St.setReg]
theorem St.setReg_ne (st : St) {i j : ℕ} (h : j ≠ i) (v : Str) :
    (st.setReg i v).regs j = st.regs j := by
  simp [St.setReg, Function.update_of_ne h]

/-- Executing statement `a` from `st` takes `c` steps and yields `st'`. -/
def Exec (O : Oracle) (a : Stmt) (st st' : St) (c : ℕ) : Prop :=
  ∀ rest : List Stmt, run O c (a :: rest, st) = (rest, st')

theorem Exec.skip (O : Oracle) (st : St) : Exec O Stmt.skip st st 1 := by
  intro rest; simp [run_succ, step]

theorem Exec.pushC (O : Oracle) (st : St) (i : ℕ) (b : Bool) :
    Exec O (Stmt.pushC i b) st (st.setReg i (b :: st.regs i)) 1 := by
  intro rest; simp [run_succ, step, St.setReg]

theorem Exec.pop (O : Oracle) (st : St) (i : ℕ) :
    Exec O (Stmt.pop i) st (st.setReg i (st.regs i).tail) 1 := by
  intro rest; simp [run_succ, step, St.setReg]

theorem Exec.copy (O : Oracle) (st : St) (i j : ℕ) :
    Exec O (Stmt.copy i j) st (st.setReg i (st.regs j)) 1 := by
  intro rest; simp [run_succ, step, St.setReg]

theorem Exec.pushQ (O : Oracle) (st : St) (i : ℕ) :
    Exec O (Stmt.pushQ i) st { st with q := st.q ++ [(st.regs i).headD false] } 1 := by
  intro rest; simp [run_succ, step]

theorem Exec.pushQC (O : Oracle) (st : St) (b : Bool) :
    Exec O (Stmt.pushQC b) st { st with q := st.q ++ [b] } 1 := by
  intro rest; simp [run_succ, step]

theorem Exec.query (O : Oracle) (st : St) (i : ℕ) :
    Exec O (Stmt.query i) st
      { regs := Function.update st.regs i (if O st.q then [true] else []),
        q := [], log := st.log ++ [st.q] } 1 := by
  intro rest; simp [run_succ, step]

theorem Exec.seq {O : Oracle} {a b : Stmt} {st st₁ st' : St} {c₁ c₂ : ℕ}
    (ha : Exec O a st st₁ c₁) (hb : Exec O b st₁ st' c₂) :
    Exec O (Stmt.seq a b) st st' (c₁ + c₂ + 1) := by
  intro rest
  rw [run_succ]
  have h : step O (Stmt.seq a b :: rest, st) = (a :: b :: rest, st) := rfl
  rw [h, show c₁ + c₂ = c₂ + c₁ from Nat.add_comm _ _, run_add, ha (b :: rest), hb rest]

theorem Exec.ifNE_pos {O : Oracle} {i : ℕ} {a b : Stmt} {st st' : St} {c : ℕ}
    (h : st.regs i ≠ []) (ha : Exec O a st st' c) :
    Exec O (Stmt.ifNE i a b) st st' (c + 1) := by
  intro rest
  rw [run_succ]
  have hs : step O (Stmt.ifNE i a b :: rest, st) = (a :: rest, st) := by simp [step, h]
  rw [hs, ha rest]

theorem Exec.ifNE_neg {O : Oracle} {i : ℕ} {a b : Stmt} {st st' : St} {c : ℕ}
    (h : st.regs i = []) (hb : Exec O b st st' c) :
    Exec O (Stmt.ifNE i a b) st st' (c + 1) := by
  intro rest
  rw [run_succ]
  have hs : step O (Stmt.ifNE i a b :: rest, st) = (b :: rest, st) := by simp [step, h]
  rw [hs, hb rest]

theorem Exec.while_done {O : Oracle} {i : ℕ} {body : Stmt} {st : St} (h : st.regs i = []) :
    Exec O (Stmt.whileNE i body) st st 1 := by
  intro rest
  rw [run_succ]
  have hs : step O (Stmt.whileNE i body :: rest, st) = (rest, st) := by simp [step, h]
  rw [hs]
  simp

theorem Exec.while_step {O : Oracle} {i : ℕ} {body : Stmt} {st st₁ st' : St} {c₁ c₂ : ℕ}
    (h : st.regs i ≠ []) (hbody : Exec O body st st₁ c₁)
    (hrest : Exec O (Stmt.whileNE i body) st₁ st' c₂) :
    Exec O (Stmt.whileNE i body) st st' (c₁ + c₂ + 1) := by
  intro rest
  rw [run_succ]
  have hs : step O (Stmt.whileNE i body :: rest, st)
      = (body :: Stmt.whileNE i body :: rest, st) := by simp [step, h]
  rw [hs, show c₁ + c₂ = c₂ + c₁ from Nat.add_comm _ _, run_add,
    hbody (Stmt.whileNE i body :: rest), hrest rest]

/-- From a big-step execution we read off the outcome of running the program for any
sufficient number of steps. -/
theorem Exec.run_of_le {O : Oracle} {a : Stmt} {st st' : St} {c T : ℕ}
    (h : Exec O a st st' c) (hT : c ≤ T) : run O T ([a], st) = ([], st') := by
  have h1 : run O c ([a], st) = ([], st') := h []
  have := run_halted_mono O hT ([a], st) (by rw [h1])
  rw [this, h1]

end CS

import RequestProject.BGS.Exec

/-!
# Relativized complexity classes

`pb k n = (n+2)^(k+1)` is the family of polynomial time/length bounds used throughout.
A language is in `PClass O` if some program, run with the oracle `O`, halts within
`pb k |x|` steps on every input and accepts exactly the members of the language;
`NPClass O` is the analogous existential (witness based) definition.
-/

namespace CS

/-- The polynomial bounds we use: `pb k n = (n+2)^(k+1)`. -/
def pb (k n : ℕ) : ℕ := (n + 2) ^ (k + 1)

theorem pb_mono_right {k n m : ℕ} (h : n ≤ m) : pb k n ≤ pb k m :=
  Nat.pow_le_pow_left (by omega) _

theorem pb_mono_left {k l n : ℕ} (h : k ≤ l) : pb k n ≤ pb l n :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem two_le_pb (k n : ℕ) : 2 ≤ pb k n := by
  have : (2:ℕ) ^ 1 ≤ (n + 2) ^ (k + 1) :=
    Nat.pow_le_pow_left (by omega) 1 |>.trans (Nat.pow_le_pow_right (by omega) (by omega))
  simpa [pb] using this

/-- The initial state on input `x` with witness `w`. -/
def initSt (x w : Str) : St :=
  { regs := fun i => if i = 0 then x else if i = 1 then w else [], q := [], log := [] }

@[simp] theorem initSt_q (x w : Str) : (initSt x w).q = [] := rfl
@[simp] theorem initSt_log (x w : Str) : (initSt x w).log = [] := rfl

/-- The machine `M`, on input `x` and witness `w`, has halted after `t` steps. -/
def Halts (M : Stmt) (O : Oracle) (x w : Str) (t : ℕ) : Prop :=
  (run O t ([M], initSt x w)).1 = []

/-- The machine `M`, on input `x` and witness `w`, has halted after `t` steps in an
accepting state (register 2 nonempty). -/
def Acc (M : Stmt) (O : Oracle) (x w : Str) (t : ℕ) : Prop :=
  (run O t ([M], initSt x w)).1 = [] ∧ (run O t ([M], initSt x w)).2.regs 2 ≠ []

theorem Halts.mono {M : Stmt} {O : Oracle} {x w : Str} {t t' : ℕ} (h : Halts M O x w t)
    (ht : t ≤ t') : Halts M O x w t' := by
  unfold Halts at *
  rw [run_halted_mono O ht _ h]
  exact h

theorem Acc.mono {M : Stmt} {O : Oracle} {x w : Str} {t t' : ℕ} (h : Acc M O x w t)
    (ht : t ≤ t') : Acc M O x w t' := by
  unfold Acc at *
  rw [run_halted_mono O ht _ h.1]
  exact h

theorem Acc_iff_of_halts {M : Stmt} {O : Oracle} {x w : Str} {t t' : ℕ}
    (h : Halts M O x w t) (ht : t ≤ t') : Acc M O x w t' ↔ Acc M O x w t := by
  unfold Acc
  rw [run_halted_mono O ht _ h]

/-- Deterministic polynomial time relative to `O`. -/
def PClass (O : Oracle) : Set (Str → Bool) :=
  {L | ∃ (M : Stmt) (k : ℕ), (∀ x : Str, Halts M O x [] (pb k x.length)) ∧
        ∀ x : Str, (L x = true ↔ Acc M O x [] (pb k x.length))}

/-- Nondeterministic polynomial time relative to `O`. -/
def NPClass (O : Oracle) : Set (Str → Bool) :=
  {L | ∃ (M : Stmt) (k : ℕ), (∀ x w : Str, Halts M O x w (pb k (x.length + w.length))) ∧
        ∀ x : Str, (L x = true ↔
          ∃ w : Str, w.length ≤ pb k x.length ∧ Acc M O x w (pb k (x.length + w.length)))}

/-! ### `P^O ⊆ NP^O` -/

theorem setReg_initSt (x w : Str) : (initSt x w).setReg 1 [] = initSt x [] := by
  unfold St.setReg initSt
  congr 1
  funext i
  by_cases h : i = 1
  · subst h; simp
  · simp [h]

/-- The program `M` preceded by an instruction clearing the witness register. -/
def clearWitness (M : Stmt) : Stmt := Stmt.seq (Stmt.copy 1 5) M

theorem run_clearWitness (O : Oracle) (M : Stmt) (x w : Str) (t : ℕ) :
    run O (t + 2) ([clearWitness M], initSt x w) = run O t ([M], initSt x []) := by
  have h1 : step O ([clearWitness M], initSt x w) = ([Stmt.copy 1 5, M], initSt x w) := rfl
  have h2 : step O ([Stmt.copy 1 5, M], initSt x w) = ([M], (initSt x w).setReg 1 []) := by
    show _ = ([M], _)
    simp [step, St.setReg, initSt]
  have : t + 2 = t + 1 + 1 := by omega
  rw [this, run_succ, h1, run_succ, h2, setReg_initSt]

theorem PClass_subset_NPClass (O : Oracle) : PClass O ⊆ NPClass O := by
  rintro L ⟨M, k, hhalt, hacc⟩
  refine ⟨clearWitness M, k + 1, ?_, ?_⟩
  · intro x w
    have hbig : pb k x.length + 2 ≤ pb (k + 1) (x.length + w.length) := by
      have h1 : pb (k + 1) x.length ≤ pb (k + 1) (x.length + w.length) :=
        pb_mono_right (by omega)
      have h2 : pb k x.length + pb k x.length ≤ pb (k + 1) x.length := by
        unfold pb
        have : (x.length + 2) ^ (k + 1) * 2 ≤ (x.length + 2) ^ (k + 1) * (x.length + 2) := by
          exact Nat.mul_le_mul_left _ (by omega)
        calc (x.length + 2) ^ (k + 1) + (x.length + 2) ^ (k + 1)
            = (x.length + 2) ^ (k + 1) * 2 := by ring
          _ ≤ (x.length + 2) ^ (k + 1) * (x.length + 2) := this
          _ = (x.length + 2) ^ (k + 1 + 1) := by ring
      have h3 := two_le_pb k x.length
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hbig
    unfold Halts
    rw [show pb (k + 1) (x.length + w.length) = (pb k x.length + d) + 2 by omega,
      run_clearWitness]
    have := (hhalt x).mono (t' := pb k x.length + d) (by omega)
    exact this
  · intro x
    rw [hacc x]
    constructor
    · intro hA
      refine ⟨[], by simp, ?_⟩
      have hbig : pb k x.length + 2 ≤ pb (k + 1) (x.length + ([] : Str).length) := by
        have h1 : pb k x.length + pb k x.length ≤ pb (k + 1) x.length := by
          unfold pb
          calc (x.length + 2) ^ (k + 1) + (x.length + 2) ^ (k + 1)
              = (x.length + 2) ^ (k + 1) * 2 := by ring
            _ ≤ (x.length + 2) ^ (k + 1) * (x.length + 2) :=
                Nat.mul_le_mul_left _ (by omega)
            _ = (x.length + 2) ^ (k + 1 + 1) := by ring
        have h3 := two_le_pb k x.length
        simp only [List.length_nil, Nat.add_zero]
        omega
      unfold Acc
      rw [show pb (k + 1) (x.length + ([] : Str).length)
            = (pb (k + 1) (x.length + ([] : Str).length) - 2) + 2 by omega,
        run_clearWitness]
      have hle : pb k x.length ≤ pb (k + 1) (x.length + ([] : Str).length) - 2 := by omega
      exact hA.mono hle
    · rintro ⟨w, -, hA⟩
      have h2 : 2 ≤ pb (k + 1) (x.length + w.length) := two_le_pb _ _
      set t := pb (k + 1) (x.length + w.length) - 2 with ht
      have hA' : Acc M O x [] t := by
        unfold Acc at hA ⊢
        rwa [show pb (k + 1) (x.length + w.length) = t + 2 by omega, run_clearWitness] at hA
      by_cases hle : pb k x.length ≤ t
      · exact (Acc_iff_of_halts (hhalt x) hle).mp hA'
      · exact hA'.mono (by omega)

end CS

import RequestProject.BGS.CheckProg

/-!
# The separating oracle `B`

`B` is built by stages.  Stage `i` diagonalizes against the `i`-th pair (program, degree):
a fresh length `n` is chosen, so large that the time bound `pb k n` is smaller than the
number `2 ^ n` of strings of length `n`.  If the machine accepts `1^n` with the oracle
built so far, no string of length `n` is ever added; otherwise a string of length `n`
that the machine did not query is added.  In both cases the machine disagrees with
`Lang B` on the input `1^n`.
-/

namespace CS

/-! ### Two auxiliary existence statements -/

/-- Polynomials are eventually dominated by `2 ^ n`. -/
theorem exists_pow_lt_two_pow (K N : ℕ) : ∃ n, N ≤ n ∧ (n + 2) ^ K < 2 ^ n := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) K (r := 2) (by norm_num)).def
    (c := 1/8) (by norm_num)
  rw [Filter.eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨max N N₀, le_max_left _ _, ?_⟩
  set n := max N N₀ with hn
  have hle : N₀ ≤ n + 2 := by have := le_max_right N N₀; omega
  have h2 := hN₀ (n + 2) hle
  simp only [norm_pow, Real.norm_natCast, Real.norm_ofNat] at h2
  have h3 : ((n : ℝ) + 2) ^ K < 2 ^ n := by
    have hrw : (1/8 : ℝ) * 2 ^ (n + 2) = 2 ^ n / 2 := by ring
    rw [hrw] at h2
    push_cast at h2
    have hpos : (0:ℝ) < 2 ^ n := by positivity
    linarith
  exact_mod_cast h3

theorem exists_diag_len (m k : ℕ) : ∃ n, m < n ∧ pb k n < 2 ^ n := by
  obtain ⟨n, hn, h⟩ := exists_pow_lt_two_pow (k + 1) (m + 1)
  exact ⟨n, by omega, h⟩

/-- A length `n` larger than `m` for which the time bound `pb k n` is below `2 ^ n`. -/
noncomputable def diagLen (m k : ℕ) : ℕ := Classical.choose (exists_diag_len m k)

theorem diagLen_gt (m k : ℕ) : m < diagLen m k :=
  (Classical.choose_spec (exists_diag_len m k)).1

theorem diagLen_pb_lt (m k : ℕ) : pb k (diagLen m k) < 2 ^ (diagLen m k) :=
  (Classical.choose_spec (exists_diag_len m k)).2

theorem exists_unqueried (Lg : List Str) (n : ℕ) (h : Lg.length < 2 ^ n) :
    ∃ u : Str, u.length = n ∧ u ∉ Lg := by
  by_contra hcon
  push_neg at hcon
  classical
  set S : Finset Str := (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)
    with hS
  have hinj : Function.Injective (fun f : Fin n → Bool => List.ofFn f) := by
    intro f g hfg
    exact List.ofFn_injective hfg
  have hcard : S.card = 2 ^ n := by
    rw [hS, Finset.card_image_of_injective _ hinj]
    simp
  have hsub : S ⊆ Lg.toFinset := by
    intro u hu
    rw [hS] at hu
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
    obtain ⟨f, rfl⟩ := hu
    exact List.mem_toFinset.mpr (hcon _ (by simp))
  have h1 := Finset.card_le_card hsub
  have h2 : Lg.toFinset.card ≤ Lg.length := Lg.toFinset_card_le
  omega

open Classical in
/-- A string of length `n` which does not occur in the list `Lg`. -/
noncomputable def unqueried (Lg : List Str) (n : ℕ) : Str :=
  if h : ∃ u : Str, u.length = n ∧ u ∉ Lg then Classical.choose h else List.replicate n true

theorem unqueried_spec (Lg : List Str) (n : ℕ) (h : Lg.length < 2 ^ n) :
    (unqueried Lg n).length = n ∧ unqueried Lg n ∉ Lg := by
  have hex := exists_unqueried Lg n h
  rw [unqueried, dif_pos hex]
  exact Classical.choose_spec hex

/-! ### The stage construction -/

/-- The program treated at stage `i`. -/
noncomputable def stageProg (i : ℕ) : Stmt := progOfNat (Nat.unpair i).1

/-- The degree treated at stage `i`. -/
def stageK (i : ℕ) : ℕ := (Nat.unpair i).2

open Classical in
/-- The stages of the construction: a bound on all lengths used so far, together with the
finite part of the oracle constructed so far. -/
noncomputable def stage : ℕ → ℕ × Oracle
  | 0 => (0, fun _ => false)
  | (i + 1) =>
      let m := (stage i).1
      let Bi := (stage i).2
      let n := diagLen m (stageK i)
      let T := pb (stageK i) n
      let x : Str := List.replicate n true
      let u := unqueried (run Bi T ([stageProg i], initSt x [])).2.log n
      if Acc (stageProg i) Bi x [] T then (max T n, Bi)
      else (max T n, fun s => Bi s || decide (s = u))

/-- The fresh length used at stage `i`. -/
noncomputable def stageN (i : ℕ) : ℕ := diagLen (stage i).1 (stageK i)

/-- The time bound used at stage `i`. -/
noncomputable def stageT (i : ℕ) : ℕ := pb (stageK i) (stageN i)

/-- The input used at stage `i`. -/
noncomputable def stageX (i : ℕ) : Str := List.replicate (stageN i) true

/-- The string possibly added at stage `i`. -/
noncomputable def stageU (i : ℕ) : Str :=
  unqueried (run (stage i).2 (stageT i) ([stageProg i], initSt (stageX i) [])).2.log (stageN i)

open Classical in
theorem stage_succ (i : ℕ) : stage (i + 1) =
    (if Acc (stageProg i) (stage i).2 (stageX i) [] (stageT i)
      then (max (stageT i) (stageN i), (stage i).2)
      else (max (stageT i) (stageN i), fun s => (stage i).2 s || decide (s = stageU i))) := rfl

theorem stage_succ_of_acc {i : ℕ} (h : Acc (stageProg i) (stage i).2 (stageX i) [] (stageT i)) :
    stage (i + 1) = (max (stageT i) (stageN i), (stage i).2) := by
  rw [stage_succ, if_pos h]

theorem stage_succ_of_not_acc {i : ℕ}
    (h : ¬ Acc (stageProg i) (stage i).2 (stageX i) [] (stageT i)) :
    stage (i + 1) =
      (max (stageT i) (stageN i), fun s => (stage i).2 s || decide (s = stageU i)) := by
  rw [stage_succ, if_neg h]

theorem stage_succ_fst (i : ℕ) : (stage (i + 1)).1 = max (stageT i) (stageN i) := by
  by_cases h : Acc (stageProg i) (stage i).2 (stageX i) [] (stageT i)
  · rw [stage_succ_of_acc h]
  · rw [stage_succ_of_not_acc h]

theorem stageN_gt (i : ℕ) : (stage i).1 < stageN i := diagLen_gt _ _

theorem stageT_lt (i : ℕ) : stageT i < 2 ^ stageN i := diagLen_pb_lt _ _

theorem stage_fst_mono_succ (i : ℕ) : (stage i).1 ≤ (stage (i + 1)).1 := by
  rw [stage_succ_fst]
  have := stageN_gt i
  omega

theorem stage_fst_mono {i j : ℕ} (h : i ≤ j) : (stage i).1 ≤ (stage j).1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ n ih =>
    refine le_trans (ih (by omega)) ?_
    rw [show i + (n + 1) = (i + n) + 1 by omega]
    exact stage_fst_mono_succ _

theorem stage_succ_snd_of_ne {i : ℕ} {s : Str} (h : s ≠ stageU i) :
    (stage (i + 1)).2 s = (stage i).2 s := by
  by_cases hA : Acc (stageProg i) (stage i).2 (stageX i) [] (stageT i)
  · rw [stage_succ_of_acc hA]
  · rw [stage_succ_of_not_acc hA]
    simp [h]

theorem stage_snd_mono_succ {i : ℕ} {s : Str} (h : (stage i).2 s = true) :
    (stage (i + 1)).2 s = true := by
  by_cases hA : Acc (stageProg i) (stage i).2 (stageX i) [] (stageT i)
  · rw [stage_succ_of_acc hA]; exact h
  · rw [stage_succ_of_not_acc hA]; simp [h]

theorem stage_snd_mono {i j : ℕ} (h : i ≤ j) {s : Str} (hs : (stage i).2 s = true) :
    (stage j).2 s = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simpa using hs
  | succ n ih =>
    rw [show i + (n + 1) = (i + n) + 1 by omega]
    exact stage_snd_mono_succ (ih (by omega))

theorem stage_succ_snd_cases {i : ℕ} {s : Str} (h : (stage (i + 1)).2 s = true) :
    (stage i).2 s = true ∨ s = stageU i := by
  by_cases hA : Acc (stageProg i) (stage i).2 (stageX i) [] (stageT i)
  · rw [stage_succ_of_acc hA] at h
    exact Or.inl h
  · rw [stage_succ_of_not_acc hA] at h
    simp only at h
    rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (of_decide_eq_true h')

/-- The log of the run at stage `i` is short enough for `stageU i` to exist. -/
theorem stageU_spec (i : ℕ) :
    (stageU i).length = stageN i ∧
      stageU i ∉ (run (stage i).2 (stageT i)
        ([stageProg i], initSt (stageX i) [])).2.log := by
  refine unqueried_spec _ _ ?_
  have h1 := log_length_run (stage i).2 (stageT i) ([stageProg i], initSt (stageX i) [])
  have h2 := stageT_lt i
  simp only [initSt_log, List.length_nil, Nat.zero_add] at h1
  omega

theorem stage_len_le : ∀ (i : ℕ) (s : Str), (stage i).2 s = true → s.length ≤ (stage i).1 := by
  intro i
  induction i with
  | zero => intro s hs; exact absurd hs (by simp [stage])
  | succ n ih =>
    intro s hs
    rcases stage_succ_snd_cases hs with h | h
    · exact le_trans (ih s h) (stage_fst_mono_succ n)
    · rw [h, (stageU_spec n).1, stage_succ_fst]
      omega

/-! ### The oracle `B` and the diagonalization -/

/-- The separating oracle. -/
noncomputable def B : Oracle := fun s => @decide (∃ i, (stage i).2 s = true)
  (Classical.propDecidable _)

theorem B_eq_true {s : Str} : B s = true ↔ ∃ i, (stage i).2 s = true := by
  simp [B]

theorem B_eq_stage (a : ℕ) (s : Str) (h : s.length ≤ (stage a).1) : B s = (stage a).2 s := by
  by_cases hst : (stage a).2 s = true
  · have : B s = true := B_eq_true.mpr ⟨a, hst⟩
    rw [this, hst]
  · have hfalse : B s = false := by
      by_contra hB
      have hBt : B s = true := by
        cases hb : B s
        · exact absurd hb hB
        · rfl
      obtain ⟨j, hj⟩ := B_eq_true.mp hBt
      -- show `s` is already in `stage a`
      have key : ∀ j : ℕ, (stage j).2 s = true → (stage a).2 s = true := by
        intro j
        induction j with
        | zero => intro h0; exact absurd h0 (by simp [stage])
        | succ n ihn =>
          intro hn
          rcases Nat.lt_or_ge n a with hna | hna
          · exact stage_snd_mono (by omega) hn
          · rcases stage_succ_snd_cases hn with h' | h'
            · exact ihn h'
            · exfalso
              have h1 : (stage a).1 ≤ (stage n).1 := stage_fst_mono hna
              have h2 : (stage n).1 < stageN n := stageN_gt n
              have h3 : s.length = stageN n := by rw [h', (stageU_spec n).1]
              omega
      exact absurd (key j hj) hst
    rw [hfalse]
    cases hb : (stage a).2 s
    · rfl
    · exact absurd hb hst

theorem Lang_mem_NPClass_B : Lang B ∈ NPClass B := Lang_mem_NPClass B

theorem Lang_not_mem_PClass_B : Lang B ∉ PClass B := by
  rintro ⟨M, k, -, hacc⟩
  classical
  set i := Nat.pair (natOfProg M) k with hi
  have hP : stageProg i = M := by simp [stageProg, hi]
  have hK : stageK i = k := by simp [stageK, hi]
  set n := stageN i with hn
  set T := stageT i with hT
  set x := stageX i with hx
  have hxlen : x.length = n := by simp [hx, stageX, hn]
  have hTpb : T = pb k x.length := by rw [hT, stageT, hK, hxlen, hn]
  -- the run with the finite oracle and the run with `B` coincide
  have hlog : ∀ s ∈ (run (stage i).2 T ([M], initSt x [])).2.log, (stage i).2 s = B s := by
    intro s hs
    have hslen : s.length ≤ T := by
      refine log_mem_length_le (stage i).2 T T ([M], initSt x []) ?_ ?_ s hs
      · simp
      · simp
    have hsle : s.length ≤ (stage (i + 1)).1 := by
      rw [stage_succ_fst]
      omega
    have hne : s ≠ stageU i := by
      intro hcon
      have := (stageU_spec i).2
      rw [← hcon, hP, ← hT, ← hx] at this
      exact this hs
    rw [B_eq_stage (i + 1) s hsle, stage_succ_snd_of_ne hne]
  have hruneq : run B T ([M], initSt x []) = run (stage i).2 T ([M], initSt x []) :=
    run_congr_of_log (stage i).2 B T _ hlog
  have hAccIff : Acc M B x [] T ↔ Acc M (stage i).2 x [] T := by
    unfold Acc
    rw [hruneq]
  by_cases hA : Acc M (stage i).2 x [] T
  · -- the machine accepts, but no string of length `n` is in `B`
    have hAccB : Acc M B x [] (pb k x.length) := by
      rw [← hTpb]
      exact hAccIff.mpr hA
    obtain ⟨u, hu, hBu⟩ := Lang_eq_true.mp ((hacc x).mpr hAccB)
    have hstage : stage (i + 1) = (max T n, (stage i).2) := by
      rw [stage_succ_of_acc (by rw [hP, ← hx, ← hT]; exact hA), ← hT, ← hn]
    have hule : u.length ≤ (stage (i + 1)).1 := by
      rw [hstage]
      simp only
      omega
    have hBu' : (stage (i + 1)).2 u = true := by rw [← B_eq_stage (i + 1) u hule]; exact hBu
    rw [hstage] at hBu'
    simp only at hBu'
    have := stage_len_le i u hBu'
    have h2 := stageN_gt i
    omega
  · -- the machine rejects, but the fresh string of length `n` is in `B`
    have hstage : stage (i + 1) =
        (max T n, fun s => (stage i).2 s || decide (s = stageU i)) := by
      rw [stage_succ_of_not_acc (by rw [hP, ← hx, ← hT]; exact hA), ← hT, ← hn]
    have hBu : B (stageU i) = true := by
      refine B_eq_true.mpr ⟨i + 1, ?_⟩
      rw [hstage]
      simp
    have hlen : (stageU i).length = x.length := by rw [(stageU_spec i).1, hxlen, hn]
    have : Lang B x = true := Lang_eq_true.mpr ⟨stageU i, hlen, hBu⟩
    have hAccB := (hacc x).mp this
    rw [← hTpb] at hAccB
    exact hA (hAccIff.mp hAccB)

theorem PClass_ne_NPClass_B : PClass B ≠ NPClass B := by
  intro h
  exact Lang_not_mem_PClass_B (h ▸ Lang_mem_NPClass_B)

end CS

import RequestProject.BGS.Programs

/-!
# The language `Lang B` and its nondeterministic polynomial time machine

`Lang B = { x | ∃ u, |u| = |x| and u ∈ B }`.  A nondeterministic machine guesses `u` and
queries the oracle about it; to avoid having to check the length of the guess, the machine
copies exactly `|x|` symbols of the witness into the query register (padding with zeros),
so that the queried string always has length exactly `|x|`.
-/

namespace CS

/-- `padTake n w` is the length-`n` string consisting of the first `n` symbols of `w`,
padded with `false`. -/
def padTake : ℕ → Str → Str
  | 0, _ => []
  | (n + 1), w => w.headD false :: padTake n w.tail

@[simp] theorem padTake_length (n : ℕ) (w : Str) : (padTake n w).length = n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [padTake, ih]

theorem padTake_self : ∀ w : Str, padTake w.length w = w := by
  intro w
  induction w with
  | nil => rfl
  | cons b r ih => simpa [padTake] using ih

/-- Copy `|regs 3|` symbols of register 4 into the query register. -/
def buildQ : Stmt :=
  Stmt.whileNE 3 (Stmt.seq (Stmt.pushQ 4) (Stmt.seq (Stmt.pop 4) (Stmt.pop 3)))

theorem buildQ_exec (O : Oracle) : ∀ (v : Str) (st : St), st.regs 3 = v →
    ∃ st' : St, Exec O buildQ st st' (6 * v.length + 1) ∧
      st'.q = st.q ++ padTake v.length (st.regs 4) ∧ st'.log = st.log := by
  intro v
  induction v with
  | nil =>
    intro st hst
    refine ⟨st, ?_, by simp [padTake], rfl⟩
    have hdone := Exec.while_done (O := O) (i := 3)
      (body := Stmt.seq (Stmt.pushQ 4) (Stmt.seq (Stmt.pop 4) (Stmt.pop 3))) (by rw [hst])
    simpa [buildQ] using hdone
  | cons b r ih =>
    intro st hst
    have hne : st.regs 3 ≠ [] := by rw [hst]; simp
    have e1 := Exec.pushQ O st 4
    set s1 : St := { st with q := st.q ++ [(st.regs 4).headD false] } with hs1
    have e2 := Exec.pop O s1 4
    set s2 : St := s1.setReg 4 (s1.regs 4).tail with hs2
    have e3 := Exec.pop O s2 3
    set s3 : St := s2.setReg 3 (s2.regs 3).tail with hs3
    have hs3r3 : s3.regs 3 = r := by
      rw [hs3, St.setReg_same, hs2, St.setReg_ne _ (by omega)]
      show (st.regs 3).tail = r
      rw [hst]; rfl
    have hs3r4 : s3.regs 4 = (st.regs 4).tail := by
      rw [hs3, St.setReg_ne _ (by omega), hs2, St.setReg_same]
    have hs3q : s3.q = st.q ++ [(st.regs 4).headD false] := rfl
    have hs3log : s3.log = st.log := rfl
    obtain ⟨st', hex, hq, hlog⟩ := ih s3 hs3r3
    refine ⟨st', ?_, ?_, by rw [hlog, hs3log]⟩
    · have hbody := Exec.seq e1 (Exec.seq e2 e3)
      have := Exec.while_step hne hbody hex
      convert this using 2
      simp
      omega
    · rw [hq, hs3q, hs3r4]
      show _ = st.q ++ padTake (r.length + 1) (st.regs 4)
      simp [padTake]

/-- The nondeterministic machine for `Lang B`. -/
def chkProg : Stmt :=
  Stmt.seq (Stmt.copy 3 0) (Stmt.seq (Stmt.copy 4 1) (Stmt.seq buildQ (Stmt.query 2)))

theorem chkProg_exec (O : Oracle) (x w : Str) :
    ∃ (st' : St) (c : ℕ), c = 6 * x.length + 7 ∧
      Exec O chkProg (initSt x w) st' c ∧
      st'.regs 2 = (if O (padTake x.length w) then [true] else []) := by
  have e1 := Exec.copy O (initSt x w) 3 0
  set s1 : St := (initSt x w).setReg 3 ((initSt x w).regs 0) with hs1
  have e2 := Exec.copy O s1 4 1
  set s2 : St := s1.setReg 4 (s1.regs 1) with hs2
  have hs2r3 : s2.regs 3 = x := by
    rw [hs2, St.setReg_ne _ (by omega), hs1, St.setReg_same]
    simp
  have hs2r4 : s2.regs 4 = w := by
    rw [hs2, St.setReg_same, hs1, St.setReg_ne _ (by omega)]
    simp
  have hs2q : s2.q = [] := rfl
  obtain ⟨s3, e3, hq3, -⟩ := buildQ_exec O x s2 hs2r3
  rw [hs2q, hs2r4] at hq3
  have e4 := Exec.query O s3 2
  refine ⟨_, _, ?_, Exec.seq e1 (Exec.seq e2 (Exec.seq e3 e4)), ?_⟩
  · omega
  · show Function.update s3.regs 2 (if O s3.q then [true] else []) 2 = _
    rw [hq3]
    simp

/-- The language `{ x | ∃ u, |u| = |x| ∧ u ∈ B }`. -/
noncomputable def Lang (B : Oracle) : Str → Bool :=
  fun x => @decide (∃ u : Str, u.length = x.length ∧ B u = true) (Classical.propDecidable _)

theorem Lang_eq_true {B : Oracle} {x : Str} :
    Lang B x = true ↔ ∃ u : Str, u.length = x.length ∧ B u = true := by
  simp [Lang]

theorem Lang_mem_NPClass (B : Oracle) : Lang B ∈ NPClass B := by
  have hcost : ∀ x w : Str, 6 * x.length + 7 ≤ pb 2 (x.length + w.length) := by
    intro x w
    have h1 : 6 * x.length + 7 ≤ (x.length + 2) ^ 3 := by nlinarith [sq_nonneg x.length]
    exact le_trans h1 (Nat.pow_le_pow_left (by omega) 3)
  refine ⟨chkProg, 2, ?_, ?_⟩
  · intro x w
    obtain ⟨st', c, hc, hex, -⟩ := chkProg_exec B x w
    unfold Halts
    rw [hex.run_of_le (by rw [hc]; exact hcost x w)]
  · intro x
    rw [Lang_eq_true]
    constructor
    · rintro ⟨u, hu, hBu⟩
      obtain ⟨st', c, hc, hex, hout⟩ := chkProg_exec B x u
      refine ⟨u, ?_, ?_⟩
      · rw [hu]
        calc x.length ≤ (x.length + 2) ^ 1 := by simp
          _ ≤ pb 2 x.length := Nat.pow_le_pow_right (by omega) (by omega)
      · unfold Acc
        rw [hex.run_of_le (by rw [hc]; exact hcost x u)]
        refine ⟨rfl, ?_⟩
        show st'.regs 2 ≠ []
        rw [hout, ← hu, padTake_self, if_pos hBu]
        simp
    · rintro ⟨w, -, hAcc⟩
      obtain ⟨st', c, hc, hex, hout⟩ := chkProg_exec B x w
      have h2 := hAcc.2
      rw [hex.run_of_le (by rw [hc]; exact hcost x w)] at h2
      have h3 : st'.regs 2 ≠ [] := h2
      rw [hout] at h3
      by_cases hB : B (padTake x.length w) = true
      · exact ⟨padTake x.length w, by simp, hB⟩
      · simp [hB] at h3

end CS

