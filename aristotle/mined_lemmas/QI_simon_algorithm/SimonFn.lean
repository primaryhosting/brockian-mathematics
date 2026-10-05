/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/

def SimonFn {n : ℕ} (s : Vec n) (f : Vec n → Vec n) : Prop :=
  (∀ x, f (x + s) = f x) ∧ (∀ x y, f x = f y → y = x ∨ y = x + s)

/-- Deterministic classical query algorithms: decision trees of depth at most `d` that
query an oracle `Vec n → Vec n` (adaptively) and finally output an element of `Vec n`. -/
inductive DTree (n : ℕ) : ℕ → Type
  | leaf {d : ℕ} (out : Vec n) : DTree n d
  | node {d : ℕ} (x : Vec n) (k : Vec n → DTree n d) : DTree n (d + 1)

/-- The output of the decision tree on oracle `f`. -/
