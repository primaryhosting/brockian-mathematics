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
## Characters and low-degree functions over `𝔽₃`

Boolean inputs are encoded multiplicatively: `true ↦ -1`, `false ↦ 1` (`CS.sgn`),
and also additively `true ↦ 1`, `false ↦ 0` (`CS.bit`).

For `S : Finset (Fin n)` the *character* `chi S` is the multilinear monomial
`x ↦ ∏ i ∈ S, sgn (x i)`; `V n D` is the space of functions `(Fin n → Bool) → 𝔽₃`
spanned by characters of degree at most `D`.
-/

namespace CS

/-- The field with three elements. -/
abbrev F : Type := ZMod 3

/-- Boolean inputs on `n` variables. -/
abbrev Inp (n : ℕ) : Type := Fin n → Bool

/-- Multiplicative (`±1`) encoding of a bit. -/

lemma chi_univ_eq (n : ℕ) (x : Inp n) :
    chi Finset.univ x = 1 + bit (parity n x) := by
  classical
  have h1 : chi (Finset.univ : Finset (Fin n)) x
      = (-1 : F) ^ (Finset.univ.filter (fun i => x i = true)).card := by
    rw [chi, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => x i = true)
      (fun i => sgn (x i))]
    rw [Finset.prod_congr rfl (g := fun _ => (-1 : F)) (fun i hi => by
        simp only [Finset.mem_filter] at hi
        simp [sgn, hi.2]),
      Finset.prod_congr rfl (s₂ := Finset.univ.filter (fun i => ¬ (x i = true)))
        (g := fun _ => (1 : F)) (fun i hi => by
        simp only [Finset.mem_filter] at hi
        simp [sgn, hi.2])]
    simp
  rw [h1, parity, bit]
  by_cases h : Odd (Finset.univ.filter (fun i => x i = true)).card
  · rw [Odd.neg_one_pow h]
    simp [h]
    decide
  · rw [Nat.not_odd_iff_even] at h
    rw [Even.neg_one_pow h]
    simp [Nat.not_odd_iff_even.2 h]

end CS

