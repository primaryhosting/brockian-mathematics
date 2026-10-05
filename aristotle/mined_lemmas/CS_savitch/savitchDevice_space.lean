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

theorem savitchDevice_space (hcard : Fintype.card (Option M.Conf) ≤ 2 ^ K) (hK : 1 ≤ K) :
    (savitchDevice M K).SpaceBound (16 * K ^ 2) := by
  have hcard2 : Fintype.card { p : St (Option M.Conf) // p.2.length ≤ K } ≤
      Fintype.card (Fin (16 * K ^ 2) → Bool) := by
    have := card_boundedSt_le_pow (C := Option M.Conf) K hcard hK
    simpa using this
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard2
  exact ⟨g, g.injective⟩

end Device

/-! ### Savitch's theorem -/

/-- **Savitch's theorem**: every language recognised by a nondeterministic device
in space `f` is recognised by a deterministic device in space `O(f²)`, namely
`16 * (f + 1)²`. -/
