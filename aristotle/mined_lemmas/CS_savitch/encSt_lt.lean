/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Interp
import RequestProject.Savitch.BigStep
import RequestProject.Savitch.Invariant
import RequestProject.Savitch.Encode

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

`NSPACE(f) ⊆ DSPACE(f²)`, and consequently `PSPACE = NPSPACE` (Savitch's theorem).

The model of computation is the standard configuration-graph model, set up in
`RequestProject.Savitch.Model`: configurations are natural numbers (binary strings), a machine
runs in space `f` on input `x` if all configurations reachable on `x` are `< 2 ^ f |x|`, and
one step may depend on the current configuration together with the single input symbol scanned
by the input head, whose position is determined by the configuration.  The initial
configuration may depend on the input length (the usual assumption that the space bound is
constructible).  No computability assumption is imposed on the transition functions.

The deterministic simulator is built explicitly: it performs the depth-first evaluation of
Savitch's divide-and-conquer recursion, its states are recursion stacks of depth at most `s`,
each frame holding boundedly many numbers `< 2 ^ s`, and the whole state is encoded as a
natural number `< 2 ^ (42 * (s + 1) ^ 2)`.  Hence a nondeterministic machine running in space
`f` is simulated deterministically in space `42 * (f + 1) ^ 2`.
-/

namespace CS

open Classical

variable {Γ : Type}

/-! ### Deterministic machines are nondeterministic machines -/

/-- A deterministic machine, viewed as a nondeterministic one. -/

theorem encSt_lt {st : St} (h : Good st) : encSt st < 2 ^ (42 * (st.s + 1) ^ 2) := by
  set s := st.s with hs
  set B := 2 ^ s + s + 4 with hB
  set d := 5 * s + 6 with hd
  have hP : encList B (stNums st) < (B + 1) ^ d :=
    encList_lt B d (stNums st) (good_nums_lt h) (good_stNums_length h)
  set P := encList B (stNums st) with hPdef
  have hpair : Nat.pair s P < (max s P + 1) ^ 2 := Nat.pair_lt_max_add_one_sq s P
  have hmax : max s P + 1 ≤ (B + 1) ^ (d + 1) := by
    have h3 : s + 1 ≤ B := by
      have : s < 2 ^ s := Nat.lt_two_pow_self
      omega
    have e1 : (B + 1) ^ d ≤ (B + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : B + 1 ≤ (B + 1) ^ (d + 1) := Nat.le_self_pow (by omega) _
    rcases le_total s P with hle | hle
    · rw [max_eq_right hle]; omega
    · rw [max_eq_left hle]; omega
  have hbase : B + 1 ≤ 2 ^ (s + 3) := by
    have h1 : s < 2 ^ s := Nat.lt_two_pow_self
    have h2 : 2 ^ (s + 3) = 8 * 2 ^ s := by ring
    omega
  calc encSt st = Nat.pair s P := rfl
    _ < (max s P + 1) ^ 2 := hpair
    _ ≤ ((B + 1) ^ (d + 1)) ^ 2 := Nat.pow_le_pow_left hmax 2
    _ = (B + 1) ^ (2 * (d + 1)) := by rw [← pow_mul]; ring_nf
    _ ≤ (2 ^ (s + 3)) ^ (2 * (d + 1)) := Nat.pow_le_pow_left hbase _
    _ = 2 ^ ((s + 3) * (2 * (d + 1))) := by rw [← pow_mul]
    _ ≤ 2 ^ (42 * (s + 1) ^ 2) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : (s + 3) * (2 * (5 * s + 6 + 1)) ≤ 42 * (s + 1) ^ 2 := by nlinarith
        simpa [hd] using this

/-- A left inverse of the encoding on states satisfying the invariant. -/
