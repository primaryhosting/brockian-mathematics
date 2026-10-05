/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above must be the very first thing in the file, and Lean forbids
-- any command (including `import`) before it. The development below is therefore written so
-- that it needs nothing beyond what is automatically available, and it compiles inside this
-- Mathlib project unchanged.

set_option autoImplicit false

namespace CS

/-- The Ackermann function, defined by recursion on the lexicographic order on `Nat × Nat`. -/
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
  termination_by m n => (m, n)

/-- The lexicographic order on `Nat × Nat`, which is the termination measure used to define
`ack`, is well founded. -/
theorem wellFounded_lex_nat :
    WellFounded (Prod.Lex (· < · : Nat → Nat → Prop) (· < · : Nat → Nat → Prop)) :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- The graph of the Ackermann recursion: `Ack m n k` says that the defining equations
`A(0, n) = n + 1`, `A(m+1, 0) = A(m, 1)`, `A(m+1, n+1) = A(m, A(m+1, n))`
derive the value `k` at the input `(m, n)`. -/
inductive Ack : Nat → Nat → Nat → Prop
  | zero (n : Nat) : Ack 0 n (n + 1)
  | succ_zero {m r : Nat} : Ack m 1 r → Ack (m + 1) 0 r
  | succ_succ {m n r s : Nat} : Ack (m + 1) n r → Ack m r s → Ack (m + 1) (n + 1) s

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by rw [ack]

@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp] theorem ack_succ_succ (m n : Nat) :
    ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

/-- Existence part of totality: `ack m n` is a value derivable from the Ackermann equations
at every input `(m, n)`. -/
theorem ack_spec (m n : Nat) : Ack m n (ack m n) := by
  induction m generalizing n with
  | zero => exact (ack_zero n) ▸ Ack.zero n
  | succ m ih =>
    induction n with
    | zero => exact (ack_succ_zero m) ▸ Ack.succ_zero (ih 1)
    | succ n ihn => exact (ack_succ_succ m n) ▸ Ack.succ_succ ihn (ih (ack (m + 1) n))

/-- Uniqueness part of totality: any value derivable from the Ackermann equations at `(m, n)`
equals `ack m n`. -/
theorem Ack.eq_ack {m n k : Nat} (h : Ack m n k) : k = ack m n := by
  induction h with
  | zero n => rw [ack_zero]
  | succ_zero _ ih => rw [ack_succ_zero]; exact ih
  | succ_succ _ _ ih1 ih2 => rw [ack_succ_succ, ← ih1]; exact ih2

/-- **The Ackermann function is total.**

The recursive equations
`A(0, n) = n + 1`, `A(m+1, 0) = A(m, 1)`, `A(m+1, n+1) = A(m, A(m+1, n))`
determine exactly one value at every input `(m, n) : Nat × Nat`. Existence holds because the
recursion is well founded for the lexicographic order on `Nat × Nat`
(see `CS.wellFounded_lex_nat`), so the total function `CS.ack` is well defined; uniqueness
holds by induction on the derivation. -/
theorem ackermann_total :
    ∀ m n : Nat, ∃ k : Nat, Ack m n k ∧ ∀ k' : Nat, Ack m n k' → k' = k :=
  fun m n => ⟨ack m n, ack_spec m n, fun _ hk => hk.eq_ack⟩

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

