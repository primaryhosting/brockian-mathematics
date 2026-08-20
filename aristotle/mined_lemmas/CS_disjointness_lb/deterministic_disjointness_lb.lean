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

theorem deterministic_disjointness_lb (n : ℕ) (p : Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hp : ComputesDisj n p) : n ≤ p.depth := by
  have hcard : (2 : ℕ) ^ n ≤ p.paths.card := by
    have himg : (Finset.univ : Finset (Finset (Fin n))).card ≤ p.paths.card := by
      refine Finset.card_le_card_of_injOn (fun x => p.transcript x xᶜ) (fun x _ => ?_) ?_
      · exact p.transcript_mem_paths x xᶜ
      · intro a _ b _ hab
        exact transcript_compl_injective hp hab
    simpa [Finset.card_univ, Fintype.card_finset] using himg
  have h2 : (2 : ℕ) ^ n ≤ 2 ^ p.depth := hcard.trans p.card_paths_le
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-!
### Randomized protocols

A public-coin randomized protocol is a probability distribution `w` over
deterministic protocols `p r`.  Its cost is the worst-case depth, and its error
on an input is the total weight of the coin values on which it errs.
-/

/-- **Randomized lower bound for set disjointness.**
Any public-coin randomized protocol which computes set disjointness on subsets of
`Fin n` with per-input error probability at most `ε`, where `ε` is small enough
that `ε · 4 ^ n < 1`, must have communication cost at least `n`.  In particular
this covers zero-error (Las Vegas) randomized protocols. -/
