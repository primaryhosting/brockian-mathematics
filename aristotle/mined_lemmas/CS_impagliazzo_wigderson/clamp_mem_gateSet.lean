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

lemma clamp_mem_gateSet {N : ℕ} (hN : 0 < N) (g : Gate) : g.clamp N ∈ gateSet N := by
  have hclamp : ∀ i : ℕ, Gate.clampIdx N i < N := by
    intro i; unfold Gate.clampIdx; split <;> omega
  cases g with
  | const b => cases b <;> simp [gateSet, Gate.clamp]
  | not a =>
    simp only [Gate.clamp, gateSet, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨_, hclamp a, rfl⟩))
  | and a b =>
    simp only [Gate.clamp, gateSet, Finset.mem_union, Finset.mem_image, Finset.mem_product,
      Finset.mem_range]
    exact Or.inl (Or.inr ⟨(_, _), ⟨hclamp a, hclamp b⟩, rfl⟩)
  | or a b =>
    simp only [Gate.clamp, gateSet, Finset.mem_union, Finset.mem_image, Finset.mem_product,
      Finset.mem_range]
    exact Or.inr ⟨(_, _), ⟨hclamp a, hclamp b⟩, rfl⟩

