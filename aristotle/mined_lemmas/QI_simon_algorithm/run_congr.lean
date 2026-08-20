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

/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


lemma run_congr (T : DTree n) (f g : Vec n → ℕ) (h : ∀ x ∈ T.queries f, f x = g x) :
    T.run g = T.run f ∧ T.queries g = T.queries f := by
  induction T with
  | leaf out => simp [run, queries]
  | node q k ih =>
      have hq : f q = g q := h q (by simp [queries])
      have h' : ∀ x ∈ (k (f q)).queries f, f x = g x := by
        intro x hx
        exact h x (by simp [queries, hx])
      obtain ⟨h1, h2⟩ := ih (f q) h'
      constructor
      · show run g (k (g q)) = run f (k (f q))
        rw [← hq]; exact h1
      · show insert q ((k (g q)).queries g) = insert q ((k (f q)).queries f)
        rw [← hq, h2]

end DTree

/-! ### The adversary function -/

/-- A fixed injective encoding of `Vec n` into `ℕ`. -/
