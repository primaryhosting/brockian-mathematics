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

lemma stEnc_inj {p q : St C} (hp : p.2.length ≤ K) (hq : q.2.length ≤ K)
    (h : stEnc K p = stEnc K q) : p = q := by
  obtain ⟨m, l⟩ := p
  obtain ⟨m', l'⟩ := q
  have hp' : l.length ≤ K := hp
  have hq' : l'.length ≤ K := hq
  have h1 : m = m' := congrArg Prod.fst h
  have h2 : ∀ i : Fin K, l[(i : ℕ)]? = l'[(i : ℕ)]? := fun i => congrFun (congrArg Prod.snd h) i
  refine Prod.ext h1 ?_
  apply List.ext_getElem?
  intro i
  by_cases hi : i < K
  · exact h2 ⟨i, hi⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- The states of the evaluator with at most `K` frames. -/
noncomputable instance instFintypeBoundedSt : Fintype { p : St C // p.2.length ≤ K } :=
  Fintype.ofInjective (fun p => stEnc K p.1)
    (fun p q h => Subtype.ext (stEnc_inj K p.2 q.2 h))

