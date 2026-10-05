/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Stack

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

`NSPACE f ⊆ DSPACE (f²)`.

Given a nondeterministic machine with at most `2 ^ (c * f n + c)` configurations we build a
deterministic machine which decides, by Savitch's midpoint recursion, whether an accepting
configuration is reachable in the configuration graph.  The deterministic machine stores an
explicit recursion stack of depth `c * f n + c + 2`, each frame holding a constant number of
configurations and indices, hence it has `2 ^ O(f n ^ 2)` configurations.

As a corollary, `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

section Construction

variable (M : NMachine)

/-- The vertices of the configuration graph: the configurations of `M`, together with an extra
sink `none` which is reachable exactly from the accepting configurations.  Thus `M` accepts iff
the sink is reachable from the initial configuration. -/
abbrev Vtx (M : NMachine) (n : ℕ) : Type := Option (M.Conf n)

instance vtxFinite (n : ℕ) : Finite (Vtx M n) := by
  haveI := M.finite n; infer_instance

noncomputable instance vtxFintype (n : ℕ) : Fintype (Vtx M n) := Fintype.ofFinite _

noncomputable instance vtxDecEq (n : ℕ) : DecidableEq (Vtx M n) := Classical.decEq _

/-- An enumeration of the vertices of the configuration graph. -/

theorem encodeValid_injective (K N : ℕ) :
    Function.Injective (encodeValid (X := X) K N) := by
  rintro ⟨⟨st1, r1⟩, hv1⟩ ⟨⟨st2, r2⟩, hv2⟩ heq
  have hr : r1 = r2 := congrArg Prod.snd heq
  have hfun := congrArg Prod.fst heq
  have hst : st1 = st2 := by
    refine List.ext_getElem? fun i => ?_
    by_cases hi : i < K + 1
    · have hi' := congrFun hfun ⟨i, hi⟩
      simp only [encodeValid] at hi'
      cases h1 : st1[i]? with
      | none =>
        cases h2 : st2[i]? with
        | none => rfl
        | some f2 =>
          rw [h1, h2] at hi'
          simp at hi'
      | some f1 =>
        cases h2 : st2[i]? with
        | none => rw [h1, h2] at hi'; simp at hi'
        | some f2 =>
          rw [h1, h2] at hi'
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at hi'
          obtain ⟨hlvl, hu, hv, hmid, hph⟩ := hi'
          have hb1 : f1.lvl ≤ K := levelsOK_le _ hv1.levels _ (List.mem_of_getElem? h1)
          have hb2 : f2.lvl ≤ K := levelsOK_le _ hv2.levels _ (List.mem_of_getElem? h2)
          have hm1 : f1.mid ≤ N := hv1.mids _ (List.mem_of_getElem? h1)
          have hm2 : f2.mid ≤ N := hv2.mids _ (List.mem_of_getElem? h2)
          have : f1 = f2 := by
            obtain ⟨a1, b1, c1, d1, e1⟩ := f1
            obtain ⟨a2, b2, c2, d2, e2⟩ := f2
            simp only at hlvl hu hv hmid hph hb1 hb2 hm1 hm2
            have : a1 = a2 := by omega
            have : d1 = d2 := by omega
            simp_all
          rw [this]
    · have hlen1 : st1.length ≤ K + 1 := levelsOK_length _ hv1.levels
      have hlen2 : st2.length ≤ K + 1 := levelsOK_length _ hv2.levels
      rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
  subst hst; subst hr; rfl

instance instFiniteValid [Finite X] (K N : ℕ) : Finite {s : SState X // Valid K N s} :=
  Finite.of_injective _ (encodeValid_injective K N)

omit [DecidableEq X] in
