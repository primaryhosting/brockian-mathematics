import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


theorem simon_algorithm :
    (∀ (n : ℕ) (s x0 y : V n), dotp s y = 1 → hadamard (simonState s x0) y = 0) ∧
    (∀ (n : ℕ) (s x0 y : V n), s ≠ 0 → dotp s y = 0 →
        ‖hadamard (simonState s x0) y‖ ^ 2 = 2 / 2 ^ n) ∧
    (∀ (n : ℕ) (s : V n), s ≠ 0 →
        ∃ Y : Finset (V n), Y.card ≤ n ∧
          ∀ v : V n, (∀ y ∈ Y, dotp y v = 0) ↔ (v = 0 ∨ v = s)) ∧
    (∀ (n d : ℕ) (T : DTree n d), 1 ≤ n → Solves T → 2 ^ (n / 2) ≤ d) :=
  ⟨fun _ s x0 y h => hadamard_simonState_eq_zero s x0 y h,
   fun _ s x0 y hs h => prob_hadamard_simonState s x0 y hs h,
   fun _ s hs => exists_small_determining_set s hs,
   fun _ _ T hn hT => classical_lower_bound T hn hT⟩

#print axioms QI.simon_algorithm

end QI

