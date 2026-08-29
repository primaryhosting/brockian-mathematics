/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Interp

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
`NSPACE f ⊆ DSPACE (16 * (f + 1)^2)`, i.e. Savitch's theorem, and the corollary
`PSPACE = NPSPACE`.

The model of computation is set up in `RequestProject.Savitch.Model`: a device is
a configuration graph with read-only access to the input tape, and the space it
uses is the number of bits needed to encode a configuration.

The proof follows the classical argument.  Given a nondeterministic device `M`
using `s` bits of space, its configuration graph (extended by a single absorbing
accepting vertex) has at most `2 ^ (s+1)` vertices, so acceptance amounts to
reachability in a graph of that size.  Reachability is computed deterministically
by the midpoint recursion `reach` of `RequestProject.Savitch.Reach`, of depth
`K = s + 1`, and this recursion is executed by the explicit stack machine of
`RequestProject.Savitch.Interp`, whose states consist of at most `K` frames, each
holding three vertices and a bit.  That machine therefore has at most
`2 ^ (16 * K ^ 2)` configurations, i.e. it runs in space `O(s²)`.
-/

namespace CS

/-! ### Counting the states of the evaluator -/

section Card

variable {C : Type} [Fintype C] (K : ℕ)

/-- Encoding of a state of the evaluator by its mode and the (padded) list of its
frames. -/

lemma walk_of_reflTransGen {a b : C} (h : Relation.ReflTransGen R a b) :
    ∃ v ℓ, Walk R v ℓ a b := by
  induction h with
  | refl => exact ⟨fun _ => a, 0, rfl, rfl, by omega⟩
  | tail hab hbc ih =>
      obtain ⟨v, ℓ, h0, hl, hstep⟩ := ih
      rename_i b' c'
      refine ⟨fun t => if t ≤ ℓ then v t else c', ℓ + 1, ?_, ?_, ?_⟩
      · simpa using h0
      · simp
      · intro j hj
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
        · have h1 : j ≤ ℓ := h.le
          have h2 : j + 1 ≤ ℓ := h
          simp only [if_pos h1, if_pos h2]
          exact hstep j h
        · subst h
          simp only [if_pos (le_refl j), if_neg (by omega : ¬ j + 1 ≤ j)]
          exact hl ▸ hbc

/-- Cutting a loop out of a walk. -/
