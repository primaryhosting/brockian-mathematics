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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Communication complexity of set disjointness

We set up the standard two-party communication model (protocol trees), prove the
rectangle property of transcripts, and deduce the fooling-set lower bound
`n ≤ depth` for any deterministic protocol computing set disjointness on subsets
of `Fin n`.  We then lift this to public-coin randomized protocols.

Scope of the randomized statement: `CS.disjointness_lb` shows that every
public-coin randomized protocol for set disjointness on `Fin n` whose per-input
error probability `ε` satisfies `ε * 4 ^ n < 1` needs at least `n` bits of
communication.  This covers in particular zero-error (Las Vegas) randomized
protocols.  The constant-error version of the bound (Kalyanasundaram–Schnitger,
Razborov), which needs the corruption/information-complexity machinery, is *not*
formalized here.
-/

namespace CS

universe u v

variable {X : Type u} {Y : Type v}

/-- A deterministic two-party communication protocol with Boolean output:
a binary tree whose internal nodes are labelled by the party that speaks
(`alice` sends a bit depending on her input `x`, `bob` on his input `y`). -/
inductive Protocol (X : Type u) (Y : Type v) where
  | leaf (o : Bool) : Protocol X Y
  | alice (f : X → Bool) (a b : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (a b : Protocol X Y) : Protocol X Y

namespace Protocol

/-- The communication cost (worst-case number of exchanged bits) of a protocol. -/

theorem card_paths_le (p : Protocol X Y) : p.paths.card ≤ 2 ^ p.depth := by
  induction p with
  | leaf o => simp [paths, depth]
  | alice f a b iha ihb =>
      refine le_trans (Finset.card_union_le _ _) ?_
      refine le_trans (add_le_add (Finset.card_image_le) (Finset.card_image_le)) ?_
      have h1 : (2 : ℕ) ^ a.depth ≤ 2 ^ (max a.depth b.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2 : ℕ) ^ b.depth ≤ 2 ^ (max a.depth b.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hsum : a.paths.card + b.paths.card
          ≤ 2 ^ (max a.depth b.depth) + 2 ^ (max a.depth b.depth) :=
        add_le_add (iha.trans h1) (ihb.trans h2)
      have hpow : (2 : ℕ) ^ (1 + max a.depth b.depth)
          = 2 ^ (max a.depth b.depth) + 2 ^ (max a.depth b.depth) := by
        rw [pow_add]; ring
      simpa [depth, hpow] using hsum
  | bob g a b iha ihb =>
      refine le_trans (Finset.card_union_le _ _) ?_
      refine le_trans (add_le_add (Finset.card_image_le) (Finset.card_image_le)) ?_
      have h1 : (2 : ℕ) ^ a.depth ≤ 2 ^ (max a.depth b.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2 : ℕ) ^ b.depth ≤ 2 ^ (max a.depth b.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hsum : a.paths.card + b.paths.card
          ≤ 2 ^ (max a.depth b.depth) + 2 ^ (max a.depth b.depth) :=
        add_le_add (iha.trans h1) (ihb.trans h2)
      have hpow : (2 : ℕ) ^ (1 + max a.depth b.depth)
          = 2 ^ (max a.depth b.depth) + 2 ^ (max a.depth b.depth) := by
        rw [pow_add]; ring
      simpa [depth, hpow] using hsum

/-- The transcript determines the output. -/
