import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

section Setup

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Partition function of the energy landscape `E k` at inverse temperature `beta`. -/

lemma prod_reverse_kernels (hDB : DetailedBalance E T beta) :
    ∏ k ∈ Finset.range N, T k (x (k + 1)) (x k)
      = (∏ k ∈ Finset.range N, T k (x k) (x (k + 1))) *
        Real.exp (-beta * ∑ k ∈ Finset.range N,
          (E (k + 1) (x k) - E (k + 1) (x (k + 1)))) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ, ih]
      have hb := hDB n (x n) (x (n + 1))
      have hkey : T n (x (n + 1)) (x n)
          = T n (x n) (x (n + 1)) *
            Real.exp (-beta * (E (n + 1) (x n) - E (n + 1) (x (n + 1)))) := by
        have hpos : (0 : ℝ) < Real.exp (-beta * E (n + 1) (x (n + 1))) := Real.exp_pos _
        have hd : Real.exp (-beta * (E (n + 1) (x n) - E (n + 1) (x (n + 1))))
            = Real.exp (-beta * E (n + 1) (x n))
              / Real.exp (-beta * E (n + 1) (x (n + 1))) := by
          rw [← Real.exp_sub]; ring_nf
        rw [hd, mul_div_assoc', eq_div_iff hpos.ne']
        linarith [hb]
      rw [hkey, mul_add, Real.exp_add]
      ring

omit [Fintype X] [Nonempty X] in
/-- Telescoping identity relating the detailed-balance exponent to the work. -/
