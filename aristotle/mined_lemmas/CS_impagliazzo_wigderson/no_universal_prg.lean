/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses only the Lean 4 core library),
so that the file can literally begin with the header comment above.

Encoding conventions:
* an input of length `n` is a natural number `x` (thought of as the bit string
  `x.testBit 0, …, x.testBit (n-1)`);
* a random string of length `r` is a natural number `ρ < 2 ^ r`;
* probabilities are handled by counting: `count r f` is the number of strings of length `r`
  on which `f` returns `true`, and a probability statement `p ≥ 2/3` is written as
  `2 * 2 ^ r ≤ 3 * count r f`.
-/

namespace CS

/-! ## Counting -/

/-- The number of strings `ρ < 2 ^ r` on which `f` returns `true`. -/

theorem no_universal_prg (r s : Nat) (gen : Nat → Nat) (h : s + 2 ≤ r) :
    ∃ A : Nat → Bool,
      ¬ 12 * (count s (fun y => A (gen y)) * 2 ^ r)
          ≤ 12 * (count r A * 2 ^ s) + 2 ^ r * 2 ^ s := by
  refine ⟨fun ρ => (List.range (2 ^ s)).any (fun y => gen y == ρ), ?_⟩
  refine distinguisher_gap (A := fun ρ => (List.range (2 ^ s)).any (fun y => gen y == ρ))
    (gen := gen) h ?_ ?_
  · have hlen : count s (fun y => (List.range (2 ^ s)).any (fun z => gen z == gen y))
        = (List.range (2 ^ s)).length := by
      rw [count, List.countP_eq_length]
      intro y hy
      simp only [List.any_eq_true]
      exact ⟨y, hy, by simp⟩
    rw [hlen, List.length_range]
  · have := countP_image_le (2 ^ r) (List.range (2 ^ s)) gen
    rw [List.length_range] at this
    exact this

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

