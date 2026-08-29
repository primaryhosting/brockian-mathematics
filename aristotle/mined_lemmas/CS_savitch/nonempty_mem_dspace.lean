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

theorem nonempty_mem_dspace (Γ : Type) :
    (fun x : List Γ => x ≠ []) ∈ DSPACE Γ (fun _ => 1) := by
  refine ⟨fun _ => nonemptyDevice Γ, fun n => ⟨fun b _ => b, ?_⟩, fun x => ?_⟩
  · intro a b h
    simpa using congrFun h 0
  · constructor
    · intro hx
      cases x with
      | nil => exact absurd rfl hx
      | cons a t =>
          refine ⟨1, ?_⟩
          show (nonemptyDevice Γ).run (a :: t) 1 = true
          rw [DDevice.run]
          rfl
    · rintro ⟨t, ht⟩
      by_contra hx
      subst hx
      have hrun : ∀ t, (nonemptyDevice Γ).run ([] : List Γ) t = false := by
        intro t
        induction t with
        | zero => rfl
        | succ t ih => rw [DDevice.run, ih]; rfl
      rw [show ((nonemptyDevice Γ).acc ((nonemptyDevice Γ).run ([] : List Γ) t)) =
        ((nonemptyDevice Γ).run ([] : List Γ) t = true) from rfl, hrun t] at ht
      exact Bool.noConfusion ht

/-- A device with no space at all has a single configuration, so it either
accepts all words or none. -/
