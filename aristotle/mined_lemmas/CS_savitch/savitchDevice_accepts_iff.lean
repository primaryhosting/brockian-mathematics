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

theorem savitchDevice_accepts_iff (x : List Γ)
    (hcard : Fintype.card (Option M.Conf) ≤ 2 ^ K) :
    (savitchDevice M K).Accepts x ↔ M.Accepts x := by
  have h1 : (savitchDevice M K).Accepts x ↔
      Reaches (savitchRun M K x) (Mode.ask (some M.init) none, []) (Mode.ret true, []) := by
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← savitchDevice_run_val M K x t]
      exact ht
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      show ((savitchDevice M K).run x t).1 = (Mode.ret true, [])
      rw [savitchDevice_run_val M K x t]
      exact ht
  rw [h1, interp_accepts_iff (isInterp_savitchRun M K x), reach_iff hcard,
    ← accepts_iff_reflTransGen]

/-- **The simulator runs in space `O(K²)`.** -/
