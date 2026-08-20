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

lemma fiber_sum {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) (y : V n) :
    ∑ b : V n, (∑ x : V n, chi (dot x y) * (if f x = b then (1 : ℝ) else 0)) ^ 2
      = 2 ^ n * (1 + chi (dot s y)) := by
  obtain ⟨hs, hfib⟩ := h
  have step1 : ∀ b : V n,
      (∑ x : V n, chi (dot x y) * (if f x = b then (1 : ℝ) else 0)) ^ 2
        = ∑ x : V n, ∑ x' : V n,
          (chi (dot x y) * (if f x = b then (1:ℝ) else 0)) *
          (chi (dot x' y) * (if f x' = b then (1:ℝ) else 0)) := by
    intro b
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun b _ => step1 b), Finset.sum_comm]
  have step2 : ∀ x : V n, ∑ b : V n, ∑ x' : V n,
      (chi (dot x y) * (if f x = b then (1:ℝ) else 0)) *
      (chi (dot x' y) * (if f x' = b then (1:ℝ) else 0))
      = ∑ x' : V n, chi (dot x y) * chi (dot x' y) * (if f x = f x' then (1:ℝ) else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_eq_single (f x)]
    · by_cases hx : f x' = f x
      · simp [hx]
      · simp [hx, Ne.symm hx]
    · intro b _ hb; simp [Ne.symm hb]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  rw [Finset.sum_congr rfl (fun x _ => step2 x)]
  have step3 : ∀ x : V n,
      (∑ x' : V n, chi (dot x y) * chi (dot x' y) * (if f x = f x' then (1:ℝ) else 0))
        = 1 + chi (dot s y) := by
    intro x
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have hset : (Finset.univ.filter (fun x' : V n => f x = f x')) = {x, x + s} := by
      ext x'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hfib x x'
    rw [hset, Finset.sum_pair (Ne.symm (add_right_ne_self hs))]
    have h1 : chi (dot x y) * chi (dot x y) = 1 := chi_mul_self _
    have h2 : chi (dot (x + s) y) = chi (dot x y) * chi (dot s y) := by
      rw [dot_add_left, chi_add]
    rw [h2]
    linear_combination (1 + chi (dot s y)) * h1
  rw [Finset.sum_congr rfl (fun x _ => step3 x)]
  simp [Finset.card_univ]
  ring

/-- **Simon's measurement law**: the outcome of one run of the circuit is uniformly
distributed over the hyperplane orthogonal to the secret `s`. -/
