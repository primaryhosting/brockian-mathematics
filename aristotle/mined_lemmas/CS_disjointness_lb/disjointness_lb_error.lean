/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
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

set_option grind.warning false

namespace CS

/-! ## The communication model

A two-party deterministic communication protocol on inputs `X` (Alice) and `Y` (Bob) is a
binary tree.  At an `alice` node the bit sent depends only on Alice's input, at a `bob` node
only on Bob's input, and a `leaf` carries the output of the protocol.  The `cost` of a protocol
is the depth of the tree, i.e. the number of bits exchanged in the worst case. -/
inductive Protocol (X Y : Type) : Type
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X Y : Type}

/-- The output of a protocol on a given pair of inputs. -/

theorem disjointness_lb_error (n : ℕ) {R : Type} [Fintype R] [Nonempty R]
    (P : R → Protocol (Inp n) (Inp n)) (c m : ℕ)
    (hcost : ∀ r, (P r).cost ≤ c)
    (hsound : ∀ (r : R) (x y : Inp n), (P r).run x y = true → Disjoint x y)
    (hcomp : ∀ x y : Inp n, Disjoint x y →
      Fintype.card R ≤ m * (Finset.univ.filter (fun r => (P r).run x y = true)).card) :
    2 ^ n ≤ m * 2 ^ c := by
  classical
  -- For each fixed random string, the number of accepted fooling pairs is at most `2 ^ c`.
  have hper : ∀ r : R,
      (Finset.univ.filter (fun S : Inp n => (P r).run S Sᶜ = true)).card ≤ 2 ^ c := fun r =>
    le_trans (accepted_fooling_card_le (P r) (hsound r)) (Nat.pow_le_pow_right (by norm_num)
      (hcost r))
  -- Double counting of the accepted (fooling pair, random string) incidences.
  have hswap :
      (∑ r : R, (Finset.univ.filter (fun S : Inp n => (P r).run S Sᶜ = true)).card)
        = ∑ S : Inp n, (Finset.univ.filter (fun r : R => (P r).run S Sᶜ = true)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : (Finset.univ : Finset (Inp n)).card * Fintype.card R
      ≤ m * ∑ S : Inp n, (Finset.univ.filter (fun r : R => (P r).run S Sᶜ = true)).card := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones (Finset.univ : Finset (Inp n)), Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro S _
    simpa using hcomp S Sᶜ disjoint_compl_right
  have hhigh :
      (∑ S : Inp n, (Finset.univ.filter (fun r : R => (P r).run S Sᶜ = true)).card)
        ≤ Fintype.card R * 2 ^ c := by
    rw [← hswap]
    calc (∑ r : R, (Finset.univ.filter (fun S : Inp n => (P r).run S Sᶜ = true)).card)
        ≤ ∑ _r : R, 2 ^ c := Finset.sum_le_sum (fun r _ => hper r)
      _ = Fintype.card R * 2 ^ c := by simp [Finset.sum_const, Finset.card_univ]
  have hcard : (Finset.univ : Finset (Inp n)).card = 2 ^ n := by simp
  have hR : 0 < Fintype.card R := Fintype.card_pos
  have hmain : 2 ^ n * Fintype.card R ≤ (m * 2 ^ c) * Fintype.card R := by
    calc 2 ^ n * Fintype.card R = (Finset.univ : Finset (Inp n)).card * Fintype.card R := by
          rw [hcard]
      _ ≤ m * ∑ S : Inp n, (Finset.univ.filter (fun r : R => (P r).run S Sᶜ = true)).card := hlow
      _ ≤ m * (Fintype.card R * 2 ^ c) := Nat.mul_le_mul_left m hhigh
      _ = (m * 2 ^ c) * Fintype.card R := by ring
  exact Nat.le_of_mul_le_mul_right hmain hR

/-- Main lower bound.  Any public-coin randomized protocol for set disjointness on a universe
of size `n` with one-sided error at most `1/2` — it never accepts a non-disjoint pair, and it
accepts every disjoint pair with probability at least `1/2` — must communicate at least
`n - 1` bits: if every protocol in the family costs at most `c`, then `n ≤ c + 1`. -/
