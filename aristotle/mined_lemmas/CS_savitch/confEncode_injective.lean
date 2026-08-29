import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem confEncode_injective : Function.Injective (confEncode (n := n) (K := K)) := by
  rintro ⟨⟨c1, l1⟩, h1⟩ ⟨⟨c2, l2⟩, h2⟩ h
  simp only [confEncode, Prod.mk.injEq, funext_iff] at h
  obtain ⟨hc, hl⟩ := h
  simp only at h1 h2
  have hll : l1 = l2 := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < K
    · exact hl ⟨i, hi⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  subst hll
  simp_all

noncomputable instance : Fintype (Conf n K) :=
  Fintype.ofInjective confEncode confEncode_injective

