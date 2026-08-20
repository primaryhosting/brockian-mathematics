/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Green–Tao theorem: *the primes contain arbitrarily long arithmetic progressions.*

This file contains

* the formal statement (`Frontier.HasArbitrarilyLongAPs Frontier.primeSet`, unfolded in
  `Frontier.GreenTaoStatement`);
* two Lean-checked reductions of it to standard conjectures, `Frontier.Green_Tao` (from the
  Erdős–Turán conjecture on arithmetic progressions, via Mathlib's divergence of the sum of
  prime reciprocals) and `Frontier.Green_Tao_of_Dickson` (from Dickson's conjecture on
  simultaneous primality of linear forms);
* unconditional base cases, `Frontier.Green_Tao_base`: an arithmetic progression of `k` primes
  exists for every `k ≤ 13`.

Every hypothesis is an explicit argument of the corresponding theorem; no axiom is introduced.
-/

namespace Frontier

/-- `IsAPIn A k a d` says that the `k`-term arithmetic progression with first term `a`
and common difference `d` is entirely contained in the set `A`. -/

theorem admissible_factorial_AP (k p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ∀ i < k, ¬ (p ∣ i * Nat.factorial k + n) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  classical
  rcases Nat.lt_or_ge k p with hkp | hpk
  · obtain ⟨x, hx⟩ : ∃ x : ZMod p, x ∉ (Finset.range k).image
        (fun i : ℕ => -((i : ZMod p) * ((Nat.factorial k : ℕ) : ZMod p))) := by
      by_contra hcon
      push_neg at hcon
      have h : (Finset.range k).image
          (fun i : ℕ => -((i : ZMod p) * ((Nat.factorial k : ℕ) : ZMod p))) = Finset.univ :=
        Finset.eq_univ_of_forall hcon
      have hcard : ((Finset.range k).image
          (fun i : ℕ => -((i : ZMod p) * ((Nat.factorial k : ℕ) : ZMod p)))).card < p := by
        calc _ ≤ (Finset.range k).card := Finset.card_image_le
          _ = k := Finset.card_range k
          _ < p := hkp
      rw [h, Finset.card_univ, ZMod.card] at hcard
      exact lt_irrefl _ hcard
    refine ⟨x.val, fun i hi hdvd => hx ?_⟩
    have h0 : ((i * Nat.factorial k + x.val : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    rw [ZMod.natCast_val, ZMod.cast_id] at h0
    have hxe : x = -((i : ZMod p) * ((Nat.factorial k : ℕ) : ZMod p)) := by linear_combination h0
    rw [hxe]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)
  · refine ⟨1, fun i hi hdvd => ?_⟩
    have h1 : p ∣ i * Nat.factorial k := Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos hpk) i
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

/-- **Green–Tao theorem from Dickson's conjecture (Lean-checked reduction).**

Applying Dickson's conjecture to the admissible tuple of linear forms `n + i · k!` (`i < k`)
produces, for each `k`, a `k`-term arithmetic progression of primes with common difference
`k!`. -/
