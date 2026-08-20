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

theorem exists_expCircuitHard : ∃ L : List Bool → Bool, ExpCircuitHard L := by
  choose F hF using fun n : ℕ =>
    exists_hard_function_list n (2 ^ (n / 100) - 1) (shannon_bound n)
  refine ⟨fun x => F x.length x, 100, by norm_num, ?_⟩
  intro n C hC
  have hCle : C.length ≤ 2 ^ (n / 100) - 1 := by
    have : C.length < 2 ^ (n / 100) := hC
    omega
  obtain ⟨x, hx, hne⟩ := hF n C hCle
  exact ⟨x, hx, by show C.eval x ≠ F x.length x; rwa [hx]⟩



/-! ## An abstract model of uniform computation -/

/-- An abstract model of uniform (deterministic) computation.  It provides the classes of
polynomial-time computable predicates and functions of one and of two string arguments,
together with the class `InE` of functions computable in time `2 ^ (O(n))`, and the three
closure properties of any reasonable machine model that we need:

* a polynomial-time predicate is a polynomial-time predicate of an extra dummy argument;
* polynomial-time predicates are closed under substitution of polynomial-time functions;
* the *majority over all strings of logarithmic length* of a polynomial-time predicate is
  again polynomial time (exhaustive search over `2 ^ O(log n) = poly(n)` many strings). -/
structure Model where
  /-- Polynomial-time decidable predicates of one string. -/
  PolyP : (List Bool → Bool) → Prop
  /-- Polynomial-time decidable predicates of two strings. -/
  PolyP2 : (List Bool → List Bool → Bool) → Prop
  /-- Polynomial-time computable functions of one string. -/
  PolyF : (List Bool → List Bool) → Prop
  /-- Polynomial-time computable functions of two strings. -/
  PolyF2 : (List Bool → List Bool → List Bool) → Prop
  /-- Predicates computable in deterministic time `2 ^ (O(n))` (the class `E`). -/
  InE : (List Bool → Bool) → Prop
  /-- Adding a dummy second argument keeps a predicate polynomial time. -/
  polyP2_of_polyP : ∀ f : List Bool → Bool, PolyP f → PolyP2 (fun x _ => f x)
  /-- Substituting a polynomial-time function into a polynomial-time predicate. -/
  polyP2_subst : ∀ (A : List Bool → List Bool → Bool) (G : List Bool → List Bool → List Bool),
    PolyP2 A → PolyF2 G → PolyP2 (fun x y => A x (G x y))
  /-- Exhaustive search over all strings of logarithmic length is polynomial time. -/
  polyP_majority_log : ∀ (f : List Bool → List Bool → Bool) (s : ℕ → ℕ),
    PolyP2 f → PolyF (fun x => List.replicate (s x.length) false) →
    (∃ c : ℕ, ∀ n : ℕ, s n ≤ c * (Nat.log 2 (n + 1) + 1)) →
    PolyP (fun x => decide (2 ^ (s x.length) <
      2 * (Finset.univ.filter
        (fun y : Fin (s x.length) → Bool => f x (List.ofFn y) = true)).card))

/-! ## Probabilities -/

/-- The fraction of strings `y ∈ {0,1}^k` on which `f` returns `true`. -/
