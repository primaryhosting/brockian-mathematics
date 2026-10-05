/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- A set of codes is *semantic* (extensional) if membership only depends on the
partial function computed by the code. -/

def Semantic (C : Set Code) : Prop :=
  ∀ cf cg : Code, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)

/-- **Rice's theorem (extended form).**
The index set of a nontrivial semantic property is not recursive: if `C` is a set of
codes whose membership depends only on the computed partial function (`hsem`), and `C`
is nontrivial (some code is in `C` and some code is not), then `C` is not decidable. -/
