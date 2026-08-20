import Mathlib
import RequestProject.QI.Spanning
import RequestProject.QI.Classical

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/--
**Simon's problem is solved with `O(n)` quantum queries but needs `Ω(2 ^ (n / 2))`
classical queries.**

The four conjuncts are:

1. *One quantum query.*  For every Simon function `f` with secret `s`, one run of the
   circuit `H ∘ U_f ∘ H` applied to `|0,0⟩` — which uses exactly one oracle query — yields
   a measurement outcome that is uniformly distributed over the hyperplane
   `s^⊥ = {y | ⟪y, s⟫ = 0}` (probability `2 / 2 ^ n` on it, `0` off it).

2. *`m` quantum queries.*  With `m` runs of the circuit (`m` queries in total), the
   outcomes determine `s` uniquely — i.e. `s` is the only nonzero solution of the linear
   system they define, so Gaussian elimination recovers it — with probability at least
   `1 - 2 ^ n / 2 ^ m`.

3. *`O(n)` queries suffice.*  Taking `m = 2 n` queries, the algorithm succeeds with
   probability at least `1 - 2 ^ (-n)`.

4. *Classical lower bound.*  Any deterministic classical query algorithm (decision tree)
   that outputs the correct secret for every Simon function on `n ≥ 2` bits has depth at
   least `2 ^ (n / 2)`, i.e. makes `Ω(2 ^ (n / 2))` queries in the worst case.
-/

theorem simonProb_sum {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) :
    ∑ y : V n, simonProb f y = 1 := by
  have hs := h.1
  have hcard := card_perp s hs
  have hpow : ((2:ℝ) ^ n) ≠ 0 := by positivity
  rw [Finset.sum_congr rfl (fun y _ => simonProb_eq h y)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h2 : ((Finset.univ.filter (fun y : V n => dot y s = 0)).card : ℝ) * 2 = 2 ^ n := by
    have h3 : ((2 * (Finset.univ.filter (fun y : V n => dot y s = 0)).card : ℕ) : ℝ)
        = ((2^n : ℕ) : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hcard
    push_cast at h3
    linarith
  field_simp
  linarith

end QI

import Mathlib

/-!
# Simon's problem: basic setup

We work with the `n`-bit vector space `V n = Fin n → ZMod 2` (bit strings of length `n`
with XOR as addition), the `ZMod 2`-valued inner product `dot`, and the associated
`±1`-valued character `chi`.

A function `f : V n → V n` *is a Simon function with secret `s`* (`IsSimon f s`) when
`s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`; i.e. `f` is two-to-one and its fibers are
the cosets of `{0, s}`.
-/

namespace QI

set_option autoImplicit false

/-- Bit strings of length `n`, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product on bit strings. -/
