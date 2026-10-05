-- Lean requires `import` to be the first command in a file; the required header
-- comment follows immediately below.
import Mathlib

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

/-!
## Overview

We formalise the PCP theorem `NP = PCP(log n, 1)` in its standard *constraint-satisfaction*
(gap-CSP) form, in the non-uniform (advice) setting.

* A **constraint** reads a constant number of bits of a Boolean assignment and applies an
  arbitrary Boolean predicate to them.
* A language `L ⊆ {0,1}*` is in `InNP` if for every input length `n` there is a
  constraint system `Ψ` with polynomially many constraints, each of arity at most a constant
  `q`, over variables `0, 1, …` (the first `n` variables carry the input `x`, the remaining
  ones are the witness/proof variables), such that `x ∈ L` iff `Ψ` has a satisfying assignment
  extending `x`.  By the Tseitin transformation this is exactly non-uniform `NP` (`NP/poly`).
* A language is in `InPCP` (i.e. in `PCP(log n, 1)`) if the same holds with a *gap*: for
  `x ∉ L` **every** assignment extending `x` satisfies at most half of the constraints.
  Reading a uniformly random constraint of the system is precisely a verifier that uses
  `O(log n)` random bits (there are polynomially many constraints) and reads `O(1)` bits of the
  input/proof, with completeness `1` and soundness error `1/2`.

The inclusion `PCP(log n, 1) ⊆ NP` is proved unconditionally (`CS.inNP_of_hasGapPCP`), as is the
*gap amplification by repetition* step `CS.hasGapPCP_half_of_hasGapPCP`, which turns any constant
gap into the gap `1/2` while keeping the arity constant and the size polynomial.

The remaining, genuinely hard, content of the PCP theorem is isolated as
`CS.GapCSPHardness`: every language in `NP` admits a constant-gap constraint system.  This is
the combinatorial core proved by Arora–Safra and Arora–Lund–Motwani–Sudan–Szegedy (and by
Dinur's gap amplification); it is *not* proved here.  `CS.pcp_theorem` derives the class
equality `NP = PCP(log n, 1)` from it, and `CS.pcp_theorem_iff` shows unconditionally that the
two statements are equivalent.
-/

namespace CS

/-- An assignment of Boolean values to the variables `0, 1, 2, …`. -/
abbrev Assignment := ℕ → Bool

/-- A local constraint: a list of queried variables together with a Boolean predicate on the
answers.  Its *arity* is the number of queried variables. -/
structure Constraint where
  /-- The variables read by the constraint. -/
  vars : List ℕ
  /-- The predicate applied to the values read. -/
  pred : List Bool → Bool

/-- Whether a constraint is satisfied by an assignment. -/

lemma satFrac_le_of_not_sat {Ψ : CSPInstance} {a : Assignment} (hΨ : Ψ ≠ [])
    (h : ¬ Sat Ψ a) : satFrac Ψ a ≤ 1 - 1 / (Ψ.length : ℚ) := by
  have hlenpos : 0 < Ψ.length := List.length_pos_iff.2 hΨ
  have hcount : Ψ.countP (fun c => c.holds a) + 1 ≤ Ψ.length := by
    by_contra hcon
    push_neg at hcon
    exact h (List.countP_eq_length.1 (le_antisymm List.countP_le_length (by omega)))
  have hQ : ((Ψ.countP (fun c => c.holds a) : ℕ) : ℚ) ≤ (Ψ.length : ℚ) - 1 := by
    have := (Nat.cast_le (α := ℚ)).2 hcount
    push_cast at this
    linarith
  have hlen : (0 : ℚ) < (Ψ.length : ℚ) := by exact_mod_cast hlenpos
  unfold satFrac
  rw [div_le_iff₀ hlen]
  have : (1 - 1 / (Ψ.length : ℚ)) * (Ψ.length : ℚ) = (Ψ.length : ℚ) - 1 := by
    field_simp
  rw [this]
  exact hQ

/-!
### `PCP(log n, 1) ⊆ NP`
-/

/-- Any PCP with soundness error `s < 1` witnesses membership in (non-uniform) `NP`:
the constraint system itself is the `NP` description. -/
