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
# AKS core: the introspective-numbers argument

This file contains the mathematical heart of the Agrawal–Kayal–Saxena primality test.
-/

namespace AKS

open Polynomial

section Introspective

variable {p : ℕ} [hp : Fact p.Prime]

/-- `m` is *introspective* for the polynomial `f` (with respect to `r`-th roots of unity in the
field `F` of characteristic `p`) if `f(y)^m = f(y^m)` for every `r`-th root of unity `y ∈ F`. -/

lemma exists_orderOf_eq_of_dvd {F : Type*} [Field F] [Finite F] {r : ℕ}
    (h : r ∣ Nat.card F - 1) : ∃ ζ : F, orderOf ζ = r := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Nat.card Fˣ = Nat.card F - 1 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_units]
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  refine ⟨((g ^ (Nat.card Fˣ / r) : Fˣ) : F), ?_⟩
  rw [orderOf_units, orderOf_pow, hord, hcard, Nat.gcd_eq_right (Nat.div_dvd_of_dvd h)]
  exact Nat.div_div_self h (by omega)

/-- If `n` is not a power of the prime `p` and `q * p = n`, then the map `(i,j) ↦ q^i * p^j`
is injective. -/
