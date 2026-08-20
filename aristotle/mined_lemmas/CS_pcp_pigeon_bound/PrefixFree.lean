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

/-- A finite set of binary codewords is *prefix-free* when no codeword is a prefix of a
different codeword. -/

def PrefixFree (S : Finset (List Bool)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u <+: v → u = v

/-- For a nonempty list, re-attaching its head to its tail returns the list. -/
