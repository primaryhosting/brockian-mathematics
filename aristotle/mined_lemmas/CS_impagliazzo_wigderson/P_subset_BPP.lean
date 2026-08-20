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

theorem p_subset_bpp (M : Model) (L : List Bool → Bool) (hL : M.P L) : M.BPP L := by
  refine ⟨fun x _ => L x, fun _ => 0, M.polyP2_of_polyP L hL, ⟨0, 0, by simp⟩, ?_⟩
  intro x
  constructor
  · intro h
    have : avgTrue 0 (fun _ : Fin 0 → Bool => L x) = 1 := by
      simp [avgTrue, h, Finset.filter_true_of_mem]
    rw [this]; norm_num
  · intro h
    have : avgTrue 0 (fun _ : Fin 0 → Bool => L x) = 0 := by
      simp [avgTrue, h]
    rw [this]; norm_num

/-! ## The Impagliazzo–Wigderson theorem -/

/-- The strong circuit lower bound hypothesis of Impagliazzo–Wigderson: some language in `E`
requires circuits of size `2 ^ (Ω(n))`. -/
