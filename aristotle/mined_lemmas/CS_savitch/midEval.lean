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

lemma midEval (h : IsInterp K R dstep) {k : ℕ}
    (ihA : ∀ (st : List (Frame C)), st.length + k = K → ∀ a b : C,
      Reaches dstep (Mode.ask a b, st) (Mode.ret (reach R k a b), st)) :
    ∀ (d i : ℕ), Fintype.card C - i = d → i < Fintype.card C →
      ∀ (st : List (Frame C)), st.length + 1 + k = K → ∀ a b : C,
      Reaches dstep (Mode.ask a (enum C i), (⟨a, b, enum C i, false⟩ : Frame C) :: st)
        (Mode.ret (reachFrom R k a b i), st) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro i hdi hi st hlen a b
    set fr : Frame C := ⟨a, b, enum C i, false⟩ with hfr
    have hlen' : (fr :: st).length + k = K := by simp [List.length_cons]; omega
    have step1 : Reaches dstep (Mode.ask a (enum C i), fr :: st)
        (Mode.ret (reach R k a (enum C i)), fr :: st) := ihA (fr :: st) hlen' a (enum C i)
    -- the "advance to the next midpoint" continuation
    have advance_ok : ∀ (fr' : Frame C), fr'.a = a → fr'.b = b → fr'.m = enum C i →
        (reach R k a (enum C i) = false ∨ reach R k (enum C i) b = false) →
        Reaches dstep (advance fr' st) (Mode.ret (reachFrom R k a b i), st) := by
      intro fr' ha hb hm hfalse
      by_cases hnext : i + 1 < Fintype.card C
      · have : advance fr' st =
            (Mode.ask a (enum C (i + 1)), (⟨a, b, enum C (i + 1), false⟩ : Frame C) :: st) := by
          unfold advance
          rw [hm, nxt_enum_some hi hnext, ha, hb]
        rw [this]
        have heq : reachFrom R k a b i = reachFrom R k a b (i + 1) := by
          rcases hfalse with hf | hf
          · exact reachFrom_succ_of_first_false hf
          · exact reachFrom_succ_of_second_false hf
        rw [heq]
        exact ihd (Fintype.card C - (i + 1)) (by omega) (i + 1) rfl hnext st hlen a b
      · have : advance fr' st = (Mode.ret false, st) := by
          unfold advance
          rw [hm, nxt_enum_none hi hnext]
        rw [this, reachFrom_last_false hi hnext hfalse]
        exact Reaches.refl _
    cases hv : reach R k a (enum C i) with
    | false =>
        refine step1.trans (Reaches.head (q := advance fr st) ?_ ?_)
        · rw [hv, h.pop]
          simp [hfr]
        · exact advance_ok fr rfl rfl rfl (Or.inl hv)
    | true =>
        have step2 : Reaches dstep (Mode.ret true, fr :: st)
            (Mode.ask (enum C i) b, (⟨a, b, enum C i, true⟩ : Frame C) :: st) := by
          apply Reaches.one
          rw [h.pop]
          simp [hfr]
        set fr2 : Frame C := ⟨a, b, enum C i, true⟩ with hfr2
        have hlen2 : (fr2 :: st).length + k = K := by simp [List.length_cons]; omega
        have step3 : Reaches dstep (Mode.ask (enum C i) b, fr2 :: st)
            (Mode.ret (reach R k (enum C i) b), fr2 :: st) := ihA (fr2 :: st) hlen2 _ _
        have hchain := (((step1.trans (by rw [hv]; exact step2)).trans step3))
        cases hw : reach R k (enum C i) b with
        | false =>
            refine hchain.trans (Reaches.head (q := advance fr2 st) ?_ ?_)
            · rw [hw, h.pop]
              simp [hfr2]
            · exact advance_ok fr2 rfl rfl rfl (Or.inr hw)
        | true =>
            refine hchain.trans (Reaches.one ?_)
            rw [hw, h.pop]
            simp [hfr2, reachFrom_true hi hv hw]

/-- Evaluating a subgoal at level `k`. -/
