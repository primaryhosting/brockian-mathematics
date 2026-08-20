/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

universe u

/-- Abstract model of the isolation engine's heap-with-ownership view.

* `edge a b` means the object `a` holds a reference to the object `b`;
* `owned v` means the isolation engine holds an ownership capability for `v`
  (an *unowned* object models a null / foreign / escaped capability);
* `root r` marks the entry points visible to the component under analysis. -/
structure Heap (V : Type u) where
  /-- Reference edges of the heap graph. -/
  edge : V → V → Prop
  /-- Ownership capability predicate. -/
  owned : V → Prop
  /-- Entry points of the component. -/
  root : V → Prop

variable {V : Type u}

/-- Reachability along reference edges (reflexive–transitive closure of `e`). -/
inductive Reach (e : V → V → Prop) : V → V → Prop
  /-- Every object reaches itself. -/
  | refl (a : V) : Reach e a a
  /-- Prefixing a reference edge to a reachability witness. -/
  | head {a b c : V} : e a b → Reach e b c → Reach e a c

/-- Appending a reference edge at the end of a reachability witness. -/

theorem no_null_escape_of_owned_invariant (H : Heap V) (I : V → Prop)
    (hroots : ∀ r, H.root r → I r)
    (hclosed : ∀ a, I a → ∀ b, H.edge a b → I b)
    (howned : ∀ a, I a → H.owned a) :
    ¬ NullEscapes H := by
  rw [null_escape_iff_unowned_reachable]
  rintro ⟨r, v, hr, hreach, hun⟩
  exact hun (howned v (Reach.closed hclosed hreach (hroots r hr)))

/-- Conversely, the absence of null escapes is always witnessed by such an
invariant, namely the set of objects reachable from the roots; so the
certificate rule above is complete as well. -/
