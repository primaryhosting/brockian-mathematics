/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean does not allow a module docstring before `import`; the header is repeated verbatim
-- as the module docstring immediately below the imports.)
import Mathlib

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
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

/-!
## Overview

We prove Ladner's theorem: *if `P ≠ NP` then there is an NP-intermediate language*, i.e. a
language in `NP` which is neither in `P` nor `NP`-complete.

Complexity theory is not available in Mathlib, so the development is carried out over an
explicit abstract model of polynomial time computation, packaged as the structure
`PolyFramework` below.  Strings are encoded as natural numbers, the *size* (bit length) of a
string `x` being `Nat.size x`, and a *language* is a function `ℕ → Bool`.

A `PolyFramework` consists of an enumeration `Red : ℕ → ℕ → ℕ` of the polynomial time
computable functions (`Red e` is the function computed by the `e`-th polynomial time program),
together with a degree function `deg` (`Red e` runs in time `(size x + 2) ^ deg e`), subject to
the standard closure properties of polynomial time:  closure under composition, pairing,
conditionals, basic arithmetic, bit counting, *clocked universal simulation* (running a program
with a unary time budget is polynomial), *bounded search* (searching a unary sized range for a
certificate is polynomial) and *iteration* (iterating a polynomial time function a unary number
of times, along an orbit whose sizes stay polynomially bounded, is polynomial).

All of these are standard true facts about polynomial time; they are taken as the hypotheses of
the theorem rather than as Lean `axiom`s, so the final result is axiom clean.
-/

namespace Ladner

/-- The number of set bits of `h` at positions `< m`. -/

def bitsBelow (m h : ℕ) : ℕ := ((List.range m).filter (fun j => h.testBit j)).length

/-- An abstract model of polynomial time computation over `ℕ` (strings encoded as naturals,
size = bit length = `Nat.size`).

`Red e` is the function computed by the `e`-th polynomial-time program, which runs within
`(Nat.size x + 2) ^ deg e` steps on input `x`.  The fields are the standard closure properties
of the class of polynomial time computable functions. -/
structure PolyFramework where
  /-- Enumeration of the polynomial time computable functions. -/
  Red : ℕ → ℕ → ℕ
  /-- The degree of the polynomial time bound of the `e`-th program. -/
  deg : ℕ → ℕ
  /-- The identity is polynomial time. -/
  mem_id : (fun x => x) ∈ Set.range Red
  /-- Constants are polynomial time. -/
  mem_const : ∀ c, (fun _ => c) ∈ Set.range Red
  /-- Polynomial time functions are closed under composition. -/
  mem_comp : ∀ g h, g ∈ Set.range Red → h ∈ Set.range Red →
    (fun x => g (h x)) ∈ Set.range Red
  /-- Polynomial time functions are closed under pairing. -/
  mem_pair : ∀ g h, g ∈ Set.range Red → h ∈ Set.range Red →
    (fun x => Nat.pair (g x) (h x)) ∈ Set.range Red
  /-- First projection of a pair is polynomial time. -/
  mem_fst : (fun x => (Nat.unpair x).1) ∈ Set.range Red
  /-- Second projection of a pair is polynomial time. -/
  mem_snd : (fun x => (Nat.unpair x).2) ∈ Set.range Red
  /-- Bit length is polynomial time. -/
  mem_size : (fun x => Nat.size x) ∈ Set.range Red
  /-- Addition is polynomial time. -/
  mem_add : (fun x => (Nat.unpair x).1 + (Nat.unpair x).2) ∈ Set.range Red
  /-- Multiplication is polynomial time. -/
  mem_mul : (fun x => (Nat.unpair x).1 * (Nat.unpair x).2) ∈ Set.range Red
  /-- Truncated subtraction is polynomial time. -/
  mem_sub : (fun x => (Nat.unpair x).1 - (Nat.unpair x).2) ∈ Set.range Red
  /-- Halving is polynomial time. -/
  mem_div2 : (fun x => x / 2) ∈ Set.range Red
  /-- Comparison is polynomial time. -/
  mem_le : (fun x => if (Nat.unpair x).1 ≤ (Nat.unpair x).2 then 1 else 0) ∈ Set.range Red
  /-- Polynomial time functions are closed under definition by cases. -/
  mem_ite : ∀ p g h, p ∈ Set.range Red → g ∈ Set.range Red → h ∈ Set.range Red →
    (fun x => if p x = 0 then g x else h x) ∈ Set.range Red
  /-- Counting the set bits below a given position is polynomial time. -/
  mem_bits : (fun x => bitsBelow (Nat.unpair x).1 (Nat.unpair x).2) ∈ Set.range Red
  /-- *Clocked universal simulation.*  On input `pair (pair e x) u`, checking whether the time
  bound of program `e` on `x` fits into the unary budget `Nat.size u` and, if so, running it,
  is polynomial time. -/
  mem_sim : (fun x =>
      if (Nat.size (Nat.unpair (Nat.unpair x).1).2 + 2) ^ deg (Nat.unpair (Nat.unpair x).1).1
          ≤ Nat.size (Nat.unpair x).2
      then Red (Nat.unpair (Nat.unpair x).1).1 (Nat.unpair (Nat.unpair x).1).2 + 1
      else 0) ∈ Set.range Red
  /-- *Bounded search.*  On input `pair x u`, searching for `y ≤ Nat.size u` with
  `Red e (pair x y) = 1` is polynomial time. -/
  mem_search : ∀ e, (fun x =>
      if ∃ y ≤ Nat.size (Nat.unpair x).2, Red e (Nat.pair (Nat.unpair x).1 y) = 1
      then 1 else 0) ∈ Set.range Red
  /-- *Iteration.*  If `g` is polynomial time and the sizes along the orbit of `s₀` under `g`
  grow polynomially, then iterating `g` a unary number of times is polynomial time. -/
  mem_iter : ∀ g, g ∈ Set.range Red → ∀ s₀ d, (∀ n, Nat.size (g^[n] s₀) ≤ (n + 2) ^ d) →
    (fun u => g^[Nat.size u] s₀) ∈ Set.range Red

variable (F : PolyFramework)

/-- The class of polynomial time computable functions of the framework `F`. -/
