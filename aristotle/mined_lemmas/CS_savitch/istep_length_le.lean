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

lemma istep_length_le (K : ℕ) (base : C → C → Bool) (p : St C) (h : p.2.length ≤ K) :
    (istep K base p).2.length ≤ K := by
  obtain ⟨mo, st⟩ := p
  have h : st.length ≤ K := h
  cases mo with
  | ask a b =>
      by_cases hl : st.length = K
      · rw [istep_ask, if_pos hl]; exact h
      · rw [istep_ask, if_neg hl]
        show st.length + 1 ≤ K
        omega
  | ret v =>
      cases st with
      | nil => rw [istep_ret_nil]; simp
      | cons fr st =>
          have hst : st.length + 1 ≤ K := h
          rw [istep_ret_cons]
          by_cases hh : fr.half
          · rw [if_pos hh]
            by_cases hv : v
            · rw [if_pos hv]; show st.length ≤ K; omega
            · rw [if_neg hv]; exact advance_length_le fr st hst
          · rw [if_neg hh]
            by_cases hv : v
            · rw [if_pos hv]; show st.length + 1 ≤ K; omega
            · rw [if_neg hv]; exact advance_length_le fr st hst

variable (K : ℕ) (R : C → C → Prop) (dstep : St C → St C)

/-- The abstract specification of one step of the evaluator: `dstep` behaves like
`istep K base` where the base-case test is the one-step reachability of `R`. -/
structure IsInterp : Prop where
  /-- at the bottom level, the machine tests `R` directly -/
  base : ∀ (a b : C) (st : List (Frame C)), st.length = K →
    dstep (Mode.ask a b, st) = (Mode.ret (reach R 0 a b), st)
  /-- above the bottom level, the machine pushes a frame with the first midpoint -/
  push : ∀ (a b : C) (st : List (Frame C)), st.length ≠ K →
    dstep (Mode.ask a b, st) = (Mode.ask a (enum C 0), ⟨a, b, enum C 0, false⟩ :: st)
  /-- returning with an empty stack: the machine halts -/
  halt : ∀ v : Bool, dstep (Mode.ret v, ([] : List (Frame C))) = (Mode.ret v, [])
  /-- returning to the caller -/
  pop : ∀ (v : Bool) (fr : Frame C) (st : List (Frame C)),
    dstep (Mode.ret v, fr :: st) =
      if fr.half then
        (if v then (Mode.ret true, st) else advance fr st)
      else
        (if v then (Mode.ask fr.m fr.b, ⟨fr.a, fr.b, fr.m, true⟩ :: st) else advance fr st)

