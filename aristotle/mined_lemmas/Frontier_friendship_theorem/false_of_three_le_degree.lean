import RequestProject.Friendship
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
# The friendship theorem (Erdős–Rényi–Sós)

If `G` is a finite graph in which every two distinct vertices have exactly one common
neighbour, then `G` has a vertex adjacent to all other vertices (a "politician").

The proof follows the classical argument:
* nonadjacent vertices have equal degrees (a length-3 walk count);
* hence a friendship graph with no politician is `d`-regular;
* a `d`-regular friendship graph has `d ^ 2 - d + 1` vertices;
* the cases `d ≤ 2` are handled directly;
* for `d ≥ 3` we pick a prime `p ∣ d - 1` and compare two computations of the trace of
  `A ^ p`, where `A` is the adjacency matrix over `ZMod p`.
-/

namespace Frontier

open Finset SimpleGraph Matrix

section Defs

variable {V : Type*} (G : SimpleGraph V)

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/

theorem false_of_three_le_degree [Nonempty V] (hG : IsFriendship G)
    (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by
  set p : ℕ := (d - 1).minFac with hp
  haveI : Fact p.Prime := ⟨Nat.minFac_prime (by omega)⟩
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hdvd : ((d - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (d - 1).minFac_dvd
  have dmod : (d : ZMod p) = 1 := by
    have hcast : ((d - 1 : ℕ) : ZMod p) = (d : ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    rw [hcast] at hdvd
    linear_combination hdvd
  -- the number of vertices is `1` mod `p`
  have hcard : ((Fintype.card V : ℕ) : ZMod p) = 1 := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hc := congrArg (fun n : ℕ => (n : ZMod p)) (card_of_regular hG hd)
    simp only [Nat.cast_add, Nat.cast_mul, dmod, one_mul] at hc
    have h0 : ((Fintype.card V - 1 : ℕ) : ZMod p) = 0 := by linear_combination hc
    have hsplit : (Fintype.card V : ℕ) = (Fintype.card V - 1) + 1 := by omega
    rw [hsplit, Nat.cast_add, h0, Nat.cast_one, zero_add]
  -- two computations of the trace of `A ^ p`
  have htr := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  rw [trace_adjMatrix, zero_pow (Fact.out (p := p.Prime)).ne_zero,
    adjMatrix_pow_mod_p_of_regular hG dmod hd hp2] at htr
  rw [Matrix.trace] at htr
  simp only [Matrix.diag_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at htr
  rw [hcard] at htr
  exact one_ne_zero htr

/-- A `d`-regular friendship graph with `d ≤ 2` has a politician. -/
