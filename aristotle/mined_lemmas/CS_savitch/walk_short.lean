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

lemma walk_short : ∀ (ℓ : ℕ) {v : ℕ → C} {a b : C}, Walk R v ℓ a b →
    ∃ v' ℓ', ℓ' < Fintype.card C ∧ Walk R v' ℓ' a b := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro v a b hw
    by_cases hlt : ℓ < Fintype.card C
    · exact ⟨v, ℓ, hlt, hw⟩
    · push_neg at hlt
      have hcard : Fintype.card C < Fintype.card (Fin (ℓ + 1)) := by
        simpa using Nat.lt_succ_of_le hlt
      obtain ⟨p, q, hpq, hval⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin (ℓ + 1) => v t) hcard
      have hne : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Fin.ext h)
      rcases lt_or_gt_of_ne hne with h | h
      · have hq : (q : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp q.isLt
        have := walk_splice hw h hq hval
        exact ih _ (by omega) this
      · have hp : (p : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp p.isLt
        have := walk_splice hw h hp hval.symm
        exact ih _ (by omega) this

/-- **Savitch's recursion is correct**: if `2 ^ k` is at least the number of
vertices, `reach R k` is reachability. -/
