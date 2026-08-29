import Mathlib

/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

A *system* consists of a finite set `V` of elements, each of which can be in one of
finitely many states `S`; a global state of the system is a function `V → S`.

The dynamics of the system are given by a transition kernel
`T : (V → S) → (V → S) → ℝ`, where `T s t` is the probability of moving to state `t`
from state `s`.

A *bipartition* of the system is a map `p : V → Bool` which is neither constantly
`true` nor constantly `false`; the two parts are `{v // p v = true}` and
`{v // p v = false}`.

The *effective information* of a bipartition `p` measures how far the dynamics is
from being the product of the dynamics of the two parts taken separately: it is the
(weighted) average over current states `s` of the `ℓ¹`-distance between the true
next-state distribution `T s ·` and the product of its two marginals on the parts.

*Integrated information* `Φ` is the infimum of the effective information over all
bipartitions ("the minimum information partition").

The target theorem states that a system which is *disconnected*, i.e. whose state
space splits into two nonempty parts that evolve independently of one another,
has `Φ = 0`.
-/

section Defs

variable {V S : Type*}

/-- Restriction of a global state `t : V → S` to the part `{v // p v = b}` of the
bipartition `p`. -/

lemma disconnected_frozen [DecidableEq V] [DecidableEq S] (q : V → Bool)
    (hq : IsBipartition q) :
    Disconnected (fun s t : V → S => if t = s then (1 : ℝ) else 0) q := by
  refine ⟨hq, ⟨fun a x => if x = a then (1 : ℝ) else 0,
    fun b y => if y = b then (1 : ℝ) else 0, ?_, ?_, ?_⟩⟩
  · intro a; simp
  · intro b; simp
  · intro s t
    by_cases h : t = s
    · subst h; simp
    · have h1 : ¬ (restrictPart q true t = restrictPart q true s ∧
          restrictPart q false t = restrictPart q false s) := by
        rintro ⟨ht, hf⟩
        exact h (by rw [← combineParts_restrictPart q t, ht, hf, combineParts_restrictPart])
      rcases not_and_or.mp h1 with h2 | h2 <;> simp [h, h2]

end Lemmas

/-- **Integrated information of a disconnected system vanishes.**

Let a system consist of finitely many elements `V`, each with finitely many possible
states `S`, evolving according to a transition kernel `T` (`T s t` = probability of
the next state being `t` given the current state `s`), and let `w` be any nonnegative
weighting of the current states.

Effective information `effectiveInfo w T p` of a bipartition `p` is the `w`-average
`ℓ¹`-distance between the true next-state distribution and the product of the
next-state marginals of the two parts of `p`, and integrated information
`Φ = phi w T` is the infimum of the effective information over all bipartitions
(the minimum information partition).

If the system is disconnected, i.e. there is a bipartition `p` (both parts nonempty)
along which the dynamics factors into two independent kernels, then `Φ = 0`. -/
