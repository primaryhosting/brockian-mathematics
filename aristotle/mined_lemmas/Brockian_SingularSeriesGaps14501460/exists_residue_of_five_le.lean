/-
# Singular Series Gaps 14501460 — Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps14501460.lean`.  The target theorem there is
stated in plain core Lean (its file has to start with a fixed header comment, which forbids
`import`s).  Here the same mathematical content is formalized in the idiomatic Mathlib way,
with tuples as `Finset ℤ`, primality as `Nat.Prime`, and residues in `ZMod p`.
-/

import Mathlib

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem exists_residue_of_five_le (p : Int) (hp : 5 ≤ p) (a1 a2 a3 a4 : Int) :
    ∃ r : Int, ∀ a ∈ [a1, a2, a3, a4], a % p ≠ r % p := by
  obtain ⟨r, hr0, hr5, h1, h2, h3, h4⟩ :=
    exists_small_avoiding (a1 % p) (a2 % p) (a3 % p) (a4 % p)
  refine ⟨r, ?_⟩
  have hrp : r % p = r := Int.emod_eq_of_lt hr0 (by omega)
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> rw [hrp] <;> assumption

/-- The tuple `{1450, 1452, 1456, 1458}` is admissible: modulo `2` and modulo `3` it misses
the class of `1451`, and for every prime `p ≥ 5` it is too short to cover all classes. -/
