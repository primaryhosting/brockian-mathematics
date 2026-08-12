import Mathlib
import RequestProject.WriteIntegrity

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

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A formal model of the write-integrity check of an isolation engine

This file formalises a small but faithful model of the *write path* of a
sandboxing / isolation engine (a protected compartment architecture, `PCA`).

The machine has a `wordBits`-bit address space, so addresses are naturals taken
modulo `N = 2 ^ wordBits`.  A compartment is described by a single `bound`: the
compartment may only write to addresses strictly below `bound`.

A write request `Req` consists of a start address, a size (number of cells
written) and a value.  The set of cells that the hardware actually touches is
`touched r`; note that the address computation *wraps around* the address space,
which is exactly what real hardware does.

Two bounds checks are modelled:

* `checkBuggy` : the classical "`addr + size ≤ bound`" check performed with
  machine (i.e. wrapping) arithmetic;
* `checkSafe`  : the same check performed with exact arithmetic.

Main results:

* `checkSafe_sound` / `checkSafe_complete` / `checkSafe_iff_sandboxed`:
  the safe check is sound and complete for the sandboxing property, so the
  engine's model exactly characterises the admissible writes.
* `checkSafe_preserves_outside`, `run_preserves_outside`: the isolation theorem
  — a whole run of accepted requests never modifies memory outside the
  compartment.
* `with_check_true_admits_forge`: the buggy check is *unsound* — there is a
  request that it accepts (`check = true`) yet which escapes the compartment,
  i.e. a forged write is admitted.
* `forge_escapes_sandbox`: that forgery really does corrupt memory outside the
  compartment.
* `checkBuggy_complete` and `checkBuggy_eq_checkSafe_of_noOverflow`: the buggy
  check is nevertheless complete and agrees with the safe check whenever the
  address computation does not overflow, so overflow is precisely the source of
  the unsoundness.
-/

namespace PCA
namespace WriteIntegrity

/-- Width of the machine address space, in bits. -/
def wordBits : ℕ := 64

/-- Size of the machine address space. -/
def N : ℕ := 2 ^ wordBits

lemma N_pos : 0 < N := Nat.two_pow_pos wordBits

/-- A memory maps addresses to values. -/
abbrev Mem := ℕ → ℕ

/-- A write request: write `val` into `size` consecutive cells starting at `addr`. -/
structure Req where
  /-- Start address of the write. -/
  addr : ℕ
  /-- Number of consecutive cells written. -/
  size : ℕ
  /-- Value written into each of those cells. -/
  val : ℕ
deriving DecidableEq, Repr

/-- The set of memory cells physically touched by a request.  Address arithmetic
wraps around the address space, as it does on real hardware. -/
def touched (r : Req) : Finset ℕ :=
  (Finset.range r.size).image (fun k => (r.addr + k) % N)

/-- A request is *sandboxed* for a compartment of size `bound` when every cell it
touches lies inside the compartment. -/
def Sandboxed (bound : ℕ) (r : Req) : Prop := ∀ a ∈ touched r, a < bound

/-- Effect of a write request on memory. -/
def applyWrite (r : Req) (m : Mem) : Mem :=
  fun a => if a ∈ touched r then r.val else m a

/-- Effect of a sequence of write requests on memory. -/
def run (m : Mem) : List Req → Mem
  | [] => m
  | r :: rs => run (applyWrite r m) rs

/-- The bounds check as performed with machine (wrapping) arithmetic. -/
def checkBuggy (bound : ℕ) (r : Req) : Bool :=
  decide ((r.addr + r.size) % N ≤ bound)

/-- The bounds check performed with exact arithmetic. -/
def checkSafe (bound : ℕ) (r : Req) : Bool :=
  decide (r.size = 0) || decide (r.addr + r.size ≤ bound)

/-- A request is well formed when its address range does not leave the address
space. -/
def WellFormed (r : Req) : Prop := r.addr + r.size ≤ N

/-! ### Basic facts about `touched` -/

lemma mem_touched_iff (r : Req) (a : ℕ) :
    a ∈ touched r ↔ ∃ k < r.size, (r.addr + k) % N = a := by
  simp [touched, Finset.mem_image, Finset.mem_range, eq_comm]

lemma touched_empty_of_size_zero {r : Req} (h : r.size = 0) : touched r = ∅ := by
  simp [touched, h]

lemma last_mem_touched {r : Req} (h : r.size ≠ 0) :
    (r.addr + (r.size - 1)) % N ∈ touched r := by
  rw [mem_touched_iff]
  exact ⟨r.size - 1, by omega, rfl⟩

lemma first_mem_touched {r : Req} (h : r.size ≠ 0) : r.addr % N ∈ touched r := by
  rw [mem_touched_iff]
  exact ⟨0, by omega, by simp⟩

/-! ### Soundness and completeness of the safe check -/

/-- **Soundness**: every request accepted by the safe check stays inside the
compartment. -/
theorem checkSafe_sound {bound : ℕ} {r : Req} (hb : bound ≤ N)
    (h : checkSafe bound r = true) : Sandboxed bound r := by
  intro a ha
  rw [mem_touched_iff] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  simp only [checkSafe, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · have hlt : r.addr + k < N := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- **Completeness**: every well-formed request that stays inside the compartment
is accepted by the safe check. -/
theorem checkSafe_complete {bound : ℕ} {r : Req} (hw : WellFormed r)
    (h : Sandboxed bound r) : checkSafe bound r = true := by
  unfold WellFormed at hw
  simp only [checkSafe, Bool.or_eq_true, decide_eq_true_eq]
  rcases Nat.eq_zero_or_pos r.size with hz | hz
  · exact Or.inl hz
  · right
    have hmem := last_mem_touched (r := r) (by omega)
    have hlt : r.addr + (r.size - 1) < N := by omega
    rw [Nat.mod_eq_of_lt hlt] at hmem
    have := h _ hmem
    omega

/-- The safe check exactly characterises the sandboxed well-formed requests:
the engine's model is both sound and complete. -/
theorem checkSafe_iff_sandboxed {bound : ℕ} {r : Req} (hb : bound ≤ N)
    (hw : WellFormed r) : checkSafe bound r = true ↔ Sandboxed bound r :=
  ⟨checkSafe_sound hb, checkSafe_complete hw⟩

/-! ### The isolation theorem for the safe check -/

/-- A sandboxed write does not change memory outside the compartment. -/
theorem applyWrite_preserves_outside {bound : ℕ} {r : Req} (h : Sandboxed bound r)
    (m : Mem) {a : ℕ} (ha : bound ≤ a) : applyWrite r m a = m a := by
  unfold applyWrite
  by_cases hmem : a ∈ touched r
  · have := h a hmem
    omega
  · simp [hmem]

/-- **Isolation, single step**: a write accepted by the safe check never modifies
memory outside the compartment. -/
theorem checkSafe_preserves_outside {bound : ℕ} {r : Req} (hb : bound ≤ N)
    (hc : checkSafe bound r = true) (m : Mem) {a : ℕ} (ha : bound ≤ a) :
    applyWrite r m a = m a :=
  applyWrite_preserves_outside (checkSafe_sound hb hc) m ha

/-- **Isolation, whole run**: if every request of a run is accepted by the safe
check, then the run does not modify any memory outside the compartment. -/
theorem run_preserves_outside {bound : ℕ} (hb : bound ≤ N) :
    ∀ (rs : List Req) (m : Mem), (∀ r ∈ rs, checkSafe bound r = true) →
      ∀ {a : ℕ}, bound ≤ a → run m rs a = m a := by
  intro rs
  induction rs with
  | nil => intro m _ a _; rfl
  | cons r rs ih =>
      intro m hall a ha
      have hr : checkSafe bound r = true := hall r (by simp)
      have hrest : ∀ r' ∈ rs, checkSafe bound r' = true := fun r' hr' =>
        hall r' (by simp [hr'])
      calc run m (r :: rs) a = run (applyWrite r m) rs a := rfl
        _ = applyWrite r m a := ih _ hrest ha
        _ = m a := checkSafe_preserves_outside hb hr m ha

/-! ### The buggy check admits forgeries -/

/-- The forged request: it starts at the very last address of the address space
and writes two cells, so the address computation wraps around. -/
def forgedReq : Req := ⟨N - 1, 2, 7⟩

/-- The compartment used in the counterexample. -/
def forgeBound : ℕ := 4096

lemma forgeBound_lt_N : forgeBound < N := by
  unfold forgeBound N wordBits; norm_num

lemma forgeBound_le_N : forgeBound ≤ N := forgeBound_lt_N.le

lemma last_addr_mem_touched_forgedReq : N - 1 ∈ touched forgedReq := by
  have hN : 0 < N := N_pos
  rw [mem_touched_iff]
  exact ⟨0, by norm_num [forgedReq], by
    simp only [forgedReq, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)⟩

lemma one_lt_N : 1 < N := by unfold N wordBits; norm_num

lemma checkBuggy_forgedReq : checkBuggy forgeBound forgedReq = true := by
  have hN : 1 < N := one_lt_N
  have h : (N - 1 + 2) % N = 1 := by
    have h1 : N - 1 + 2 = 1 + N := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp only [checkBuggy, forgedReq, h, decide_eq_true_eq]
  unfold forgeBound; norm_num

lemma forgedReq_not_sandboxed : ¬ Sandboxed forgeBound forgedReq := by
  intro h
  have hb := h _ last_addr_mem_touched_forgedReq
  have : forgeBound < N := forgeBound_lt_N
  omega

/-- **Unsoundness of the buggy check**: there is a compartment and a write request
that the engine's bounds check accepts, yet which escapes the compartment.  In
other words, `check = true` still admits a forged write. -/
theorem with_check_true_admits_forge :
    ∃ (bound : ℕ) (r : Req),
      bound ≤ N ∧ ¬ WellFormed r ∧ checkBuggy bound r = true ∧ ¬ Sandboxed bound r := by
  refine ⟨forgeBound, forgedReq, forgeBound_le_N, ?_, checkBuggy_forgedReq,
    forgedReq_not_sandboxed⟩
  have hN : 0 < N := N_pos
  simp only [WellFormed, forgedReq, not_le]
  omega

/-- The forgery is not merely accepted: it really does corrupt memory outside the
compartment. -/
theorem forge_escapes_sandbox :
    ∃ (bound : ℕ) (r : Req) (m : Mem) (a : ℕ),
      bound ≤ N ∧ checkBuggy bound r = true ∧ bound ≤ a ∧ applyWrite r m a ≠ m a := by
  refine ⟨forgeBound, forgedReq, (fun _ => 0), N - 1, forgeBound_le_N,
    checkBuggy_forgedReq, ?_, ?_⟩
  · have h1 : forgeBound < N := forgeBound_lt_N
    have h2 : 0 < N := N_pos
    omega
  · show (if N - 1 ∈ touched forgedReq then forgedReq.val else (0 : ℕ)) ≠ 0
    rw [if_pos last_addr_mem_touched_forgedReq]
    norm_num [forgedReq]

/-! ### The buggy check is complete, and agrees with the safe one absent overflow -/

/-- The buggy check is complete: it never rejects a well-formed sandboxed
(non-empty) request.  Hence unsoundness is its only defect. -/
theorem checkBuggy_complete {bound : ℕ} {r : Req} (hw : WellFormed r) (hz : r.size ≠ 0)
    (h : Sandboxed bound r) : checkBuggy bound r = true := by
  unfold WellFormed at hw
  simp only [checkBuggy, decide_eq_true_eq]
  have hmem := last_mem_touched (r := r) hz
  have hlt : r.addr + (r.size - 1) < N := by omega
  rw [Nat.mod_eq_of_lt hlt] at hmem
  have hb := h _ hmem
  rcases Nat.lt_or_ge (r.addr + r.size) N with hlt' | hge'
  · rw [Nat.mod_eq_of_lt hlt']; omega
  · have hEq : r.addr + r.size = N := by omega
    rw [hEq, Nat.mod_self]
    omega

/-- Absent address-space overflow the two checks agree; overflow is precisely the
source of the unsoundness. -/
theorem checkBuggy_eq_checkSafe_of_noOverflow {bound : ℕ} {r : Req}
    (hw : r.addr + r.size < N) (hz : r.size ≠ 0) :
    checkBuggy bound r = checkSafe bound r := by
  unfold checkBuggy checkSafe
  rw [Nat.mod_eq_of_lt hw]
  simp [hz]

end WriteIntegrity
end PCA

