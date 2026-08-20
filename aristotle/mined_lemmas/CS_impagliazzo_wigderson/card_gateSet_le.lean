/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-! ## Boolean circuits (straight-line programs) -/

/-- A single gate of a straight-line Boolean program.  Arguments refer to positions in the
current environment (first the input bits, then the values of the previously computed gates).
Out-of-range references evaluate to `false`. -/
inductive Gate
  | const (b : Bool)
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)
deriving DecidableEq

/-- A Boolean circuit is a straight-line program, i.e. a list of gates. -/
abbrev Circuit := List Gate

/-- Value of a single gate in a given environment. -/

lemma card_gateSet_le (N : ℕ) : (gateSet N).card ≤ 2 + N + 2 * N ^ 2 := by
  have h1 : (({Gate.const false, Gate.const true} : Finset Gate)).card ≤ 2 :=
    Finset.card_insert_le _ _ |>.trans (by simp)
  have h2 : ((Finset.range N).image Gate.not).card ≤ N := by
    simpa using Finset.card_image_le (s := Finset.range N) (f := Gate.not)
  have h3 : (((Finset.range N) ×ˢ (Finset.range N)).image
      (fun p : ℕ × ℕ => Gate.and p.1 p.2)).card ≤ N ^ 2 := by
    refine le_trans (Finset.card_image_le) ?_
    simp [Finset.card_product, sq]
  have h4 : (((Finset.range N) ×ˢ (Finset.range N)).image
      (fun p : ℕ × ℕ => Gate.or p.1 p.2)).card ≤ N ^ 2 := by
    refine le_trans (Finset.card_image_le) ?_
    simp [Finset.card_product, sq]
  have := Finset.card_union_le
    (((({Gate.const false, Gate.const true} : Finset Gate)
      ∪ (Finset.range N).image Gate.not)
      ∪ ((Finset.range N) ×ˢ (Finset.range N)).image (fun p : ℕ × ℕ => Gate.and p.1 p.2)))
    (((Finset.range N) ×ˢ (Finset.range N)).image (fun p : ℕ × ℕ => Gate.or p.1 p.2))
  have h5 := Finset.card_union_le
    ((({Gate.const false, Gate.const true} : Finset Gate)
      ∪ (Finset.range N).image Gate.not))
    (((Finset.range N) ×ˢ (Finset.range N)).image (fun p : ℕ × ℕ => Gate.and p.1 p.2))
  have h6 := Finset.card_union_le
    (({Gate.const false, Gate.const true} : Finset Gate))
    ((Finset.range N).image Gate.not)
  unfold gateSet
  omega

/-- **Shannon's counting bound.**  If there are fewer circuit codes of size `s` than Boolean
functions on `n` bits, then some Boolean function on `n` bits is not computed by any circuit
of size at most `s`. -/
