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

import Mathlib

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The relativization barrier

We formalize the Baker–Gill–Solovay theorem in a *relativized query model* of
computation:

* A **string** is a `List Bool`, a **language** (equivalently an oracle) is a
  Boolean-valued function on strings.
* An **oracle machine** is given by a *computable* transition function
  `step : α × Trans → Str ⊕ Bool`, which, given the input and the transcript of
  the queries asked so far together with the oracle's answers, either asks a new
  query (`Sum.inl z`) or halts with a verdict (`Sum.inr b`).
* The resource that is counted is the number of steps (each step is either one
  oracle query or the final answer), and a machine is *polynomially bounded*
  when it is run for `c * (n+1)^d` steps on inputs of length `n`.

`PClass A` is the class of languages decided by a polynomially bounded
deterministic oracle machine with oracle `A`; `NPClass A` is the class of
languages accepted with a polynomially long certificate by a polynomially
bounded verifier with oracle `A`.

The theorem `CS.baker_gill_solovay` states that there is an oracle `A` with
`PClass A = NPClass A` and an oracle `B` with `PClass B ≠ NPClass B`.

Two features of this model should be kept in mind. Machines are required to be
computable, so there are only countably many of them, which is what makes the
diagonalization for `B` possible; and the amount of computation performed
between two queries is unrestricted, only the number of steps is. Consequently
the collapsing oracle can be taken to be the empty oracle `emptyLang`: with no
useful oracle, both classes consist exactly of the decidable languages, since a
deterministic machine may scan all polynomially long certificates in a single
step. The separating oracle `B` is built by the usual stage construction: at
stage `i` one diagonalizes against the `i`-th machine at a length `N` where the
machine's step bound is smaller than the number `2 ^ N` of candidate strings.
-/

namespace CS

/-- Strings are finite bit sequences. -/
abbrev Str := List Bool

/-- A language, equivalently an oracle, is an indicator function on strings. -/
abbrev Lang := Str → Bool

/-- A transcript records the queries made so far together with their answers. -/
abbrev Trans := List (Str × Bool)

/-- An oracle machine with input type `α`: a computable function which, from the
input and the transcript so far, either issues a new oracle query or halts with
a verdict. -/
structure Machine (α : Type) [Primcodable α] : Type where
  /-- The transition function. -/
  step : α × Trans → Str ⊕ Bool
  /-- The transition function is computable. -/
  hstep : Computable step

section Model

variable {α : Type} [Primcodable α]

/-- A configuration: the input, the transcript so far, and the verdict (if the
machine has already halted). -/
abbrev Config (α : Type) := α × Trans × Option Bool

/-- One step of the machine with oracle `O`. -/

theorem LB_not_mem_P (hE : Function.Surjective E) :
    LB (oracleB E) ∉ PClass (oracleB E) := by
  rintro ⟨M, c, d, hM⟩
  obtain ⟨i, hi⟩ := hE (M, c, d)
  have hM1 : (E i).1 = M := by rw [hi]
  have hc : (E i).2.1 = c := by rw [hi]
  have hd : (E i).2.2 = d := by rw [hi]
  set n := (stage E i).1 with hn
  set F := (stage E i).2 with hF
  set N := diagN E i n with hN
  set Q := diagQ E i n F with hQ
  have hxlen : (diagX E i n).length = N := by rw [diagX]; simp [hN]
  have hbud : polyBound c d (diagX E i n).length = diagB E i n := by
    rw [hxlen, diagB, hc, hd, ← hN]
  have hfront : (stage E (i + 1)).1 = diagFront E i n F := stage_succ_fst E i
  have hNlt : N < (stage E (i + 1)).1 := by
    have h2 : N + 1 ≤ diagFront E i n F := le_max_left _ _
    omega
  have hQlt : ∀ z ∈ Q, z.length < (stage E (i + 1)).1 := by
    intro z hz
    have h1 := le_maxLen hz
    have h2 : maxLen Q + 1 ≤ diagFront E i n F := le_max_right _ _
    omega
  have hmemiff : ∀ z ∈ Q, (z ∈ (stage E (i + 1)).2 ↔ z ∈ F) := by
    intro z hz
    rcases stage_succ_snd E i with h | h
    · rw [h]
    · rw [h, Finset.mem_insert]
      constructor
      · rintro (rfl | hzF)
        · exact absurd hz (pick_spec (diag_exists_unqueried E i n F)).2
        · exact hzF
      · exact fun h => Or.inr h
  have hagree : ∀ z ∈ queries (E i).1 (orc F) (diagX E i n) (diagB E i n),
      orc F z = oracleB E z := by
    intro z hz
    have hz' : z ∈ Q := hz
    rw [oracleB_eq E (i + 1) (hQlt z hz')]
    exact decide_eq_decide.mpr (hmemiff z hz').symm
  have hrun : run (E i).1 (oracleB E) (diagX E i n) (diagB E i n) = diagR E i n F :=
    run_congr _ _ _ _ _ hagree
  have hMrun : diagR E i n F = some (LB (oracleB E) (diagX E i n)) := by
    have h := hM (diagX E i n)
    rw [hbud, ← hM1] at h
    rw [← hrun]
    exact h
  by_cases hcase : diagR E i n F = some true
  · have hLB : LB (oracleB E) (diagX E i n) ≠ true := by
      intro hLBt
      obtain ⟨w, hw, hBw⟩ := existsIn_eq_true.mp hLBt
      have hwlen : w.length = N := by rw [mem_allStr.mp hw, hxlen]
      have hwlt : w.length < (stage E (i + 1)).1 := by omega
      have heq : oracleB E w = decide (w ∈ (stage E (i + 1)).2) := oracleB_eq E (i + 1) hwlt
      rw [hBw] at heq
      have hmem : w ∈ (stage E (i + 1)).2 := by
        by_contra hc'
        simp [hc'] at heq
      rw [stage_succ_of_true E i hcase] at hmem
      have h1 := stage_len_lt E i w hmem
      have h2 : n ≤ N := le_max_left _ _
      omega
    rw [hcase] at hMrun
    exact hLB (Option.some_injective _ hMrun).symm
  · have hp := pick_spec (diag_exists_unqueried E i n F)
    have hpmem : pick N Q ∈ (stage E (i + 1)).2 := by
      rw [stage_succ_of_false E i hcase]
      exact Finset.mem_insert_self _ _
    have hpB : oracleB E (pick N Q) = true := by
      have hex : ∃ j, pick N Q ∈ (stage E j).2 := ⟨i + 1, hpmem⟩
      simpa [oracleB] using hex
    have hLB : LB (oracleB E) (diagX E i n) = true := by
      refine existsIn_eq_true.mpr ⟨pick N Q, ?_, hpB⟩
      rw [mem_allStr, hxlen]
      exact hp.1
    rw [hLB] at hMrun
    exact hcase hMrun

end Separation

instance : Nonempty (Machine Str) := ⟨constMachine (fun _ => false) (Computable.const false)⟩

