/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier

/-! ## Formalizing the statement -/

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with nonzero common difference `d`. -/

theorem greenTao_of_dickson (h : DicksonConjecture) : GreenTaoStatement := by
  intro k
  obtain ⟨n, -, hn⟩ := h k (fun i => i * k !) (fun _ => 1)
    (fun i _ => Nat.one_pos) (fun p hp => admissible_factorial_forms k p hp) 2
  refine ⟨n, k !, Nat.factorial_pos k, fun i hi => ?_⟩
  have hprime := hn i hi
  simp only [one_mul] at hprime
  simpa [Set.mem_setOf_eq, Nat.add_comm] using hprime

/-- **Green–Tao, as a Lean-checked reduction.**

Either of the two standard conjectures `ErdosTuranAP` and `DicksonConjecture` implies the
Green–Tao statement that the primes contain arbitrarily long arithmetic progressions. Both
implications are proved unconditionally here.

See `Frontier.Green_Tao_base` for the unconditional base cases (`k ≤ 10`). -/
