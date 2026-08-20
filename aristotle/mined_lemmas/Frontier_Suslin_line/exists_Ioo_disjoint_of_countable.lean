import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc): every family of pairwise disjoint nonempty open
sets is countable. -/

theorem exists_Ioo_disjoint_of_countable [DenselyOrdered X]
    (h : IsSuslinLine X) {C : Set X} (hC : C.Countable) :
    ∃ a b : X, a < b ∧ (Set.Ioo a b).Nonempty ∧ Disjoint (Set.Ioo a b) C := by
  haveI : Uncountable X := uncountable_of_isSuslinLine h
  haveI : Nontrivial X := by
    rcases exists_pair_ne X with ⟨x, y, hxy⟩
    exact ⟨x, y, hxy⟩
  have hnd : ¬ Dense C := by
    intro hd
    exact h.2 ⟨⟨C, hC, hd⟩⟩
  -- the complement of the closure of `C` is a nonempty open set
  have hopen : IsOpen (closure C)ᶜ := isClosed_closure.isOpen_compl
  have hnonempty : ((closure C)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro hcl
    exact hnd (dense_iff_closure_eq.mpr hcl)
  obtain ⟨a, b, hab, hsub⟩ := hopen.exists_Ioo_subset hnonempty
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact Set.nonempty_Ioo.mpr hab
  · refine Set.disjoint_left.mpr fun x hx hxC => ?_
    exact hsub hx (subset_closure hxC)

/-! ## A left-separated `ω₁`-sequence in any non-separable space

The classical construction of a Suslin tree from a Suslin line proceeds by transfinite recursion
of length `ω₁`, at each step using non-separability to find a point (indeed an interval) outside
the closure of what has been chosen so far.  We carry out this recursion here. -/

open Classical in
/-- The transfinite sequence obtained by repeatedly choosing, if possible, a point outside the
closure of the previously chosen points. -/
