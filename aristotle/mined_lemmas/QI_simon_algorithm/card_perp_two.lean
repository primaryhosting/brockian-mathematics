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

lemma card_perp_two {n : ℕ} (u v : V n) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    4 * (Finset.univ.filter (fun y : V n => dot y u = 0 ∧ dot y v = 0)).card = 2 ^ n := by
  have huv' : u + v ≠ 0 := by
    intro h
    apply huv
    have : u + v + v = 0 + v := by rw [h]
    rwa [add_add_cancel_V, zero_add] at this
  have key : ((Finset.univ.filter (fun y : V n => dot y u = 0 ∧ dot y v = 0)).card : ℝ) * 4
      = 2 ^ n := by
    have h1 : ((Finset.univ.filter (fun y : V n => dot y u = 0 ∧ dot y v = 0)).card : ℝ)
        = ∑ y : V n, ((if dot y u = 0 then (1:ℝ) else 0) * (if dot y v = 0 then (1:ℝ) else 0)) := by
      rw [Finset.sum_congr rfl (fun y _ => by
        by_cases h1 : dot y u = 0 <;> by_cases h2 : dot y v = 0 <;>
          simp [h1, h2] :
        ∀ y ∈ (Finset.univ : Finset (V n)), _ = if (dot y u = 0 ∧ dot y v = 0) then (1:ℝ) else 0)]
      simp
    rw [h1]
    have h2 : ∀ y : V n,
        (if dot y u = 0 then (1:ℝ) else 0) * (if dot y v = 0 then (1:ℝ) else 0)
          = (1 + chi (dot y u) + chi (dot y v) + chi (dot y (u + v))) / 4 := by
      intro y
      rw [indicator_eq, indicator_eq, dot_add_right, chi_add]
      ring
    rw [Finset.sum_congr rfl (fun y _ => h2 y)]
    rw [← Finset.sum_div]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [char_sum u, char_sum v, char_sum (u + v), if_neg hu, if_neg hv, if_neg huv']
    simp
  have : ((4 * (Finset.univ.filter (fun y : V n => dot y u = 0 ∧ dot y v = 0)).card : ℕ) : ℝ)
      = ((2 ^ n : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

end QI

import RequestProject.QI.Quantum

/-!
# Simon's quantum algorithm: `O(n)` queries suffice

Each run of the Simon circuit costs one query and returns a uniformly random element of
`s^⊥`.  A list `v : Fin m → V n` of outcomes *determines* `s` when the only solutions `t`
of the linear system `⟪v i, t⟫ = 0` are `t = 0` and `t = s`; in that case the classical
post-processing (Gaussian elimination) recovers `s`.

The main result is that `m` runs (hence `m` queries) determine `s` with probability at
least `1 - 2 ^ n / 2 ^ m`; with `m = 2 n` queries the failure probability is at most
`2 ^ (-n)`.
-/

namespace QI

set_option autoImplicit false

/-- The measurement outcomes `v` determine the secret `s`: the only solutions of the
homogeneous linear system they define are `0` and `s`. -/
