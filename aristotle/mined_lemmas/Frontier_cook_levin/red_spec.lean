import Mathlib
import RequestProject.Hardness

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Cook–Levin theorem

`SAT` is NP-complete:

* `SAT ∈ NP`, and
* every language in `NP` reduces to `SAT`.

Here languages are sets of bit strings; a language is in `NP` when it is decided by a
family of polynomial size Boolean circuits reading the input word together with a
witness word of polynomial length (`Frontier.InNP`).  `SAT` is the set of bit strings
whose associated CNF formula is satisfiable (`Frontier.SATlang`), the association being
the occurrence-matrix encoding of `Frontier.decodeCNF`.

The reductions produced here are *projections*: each output bit is a constant, or a bit
of the input word, or the negation of a bit of the input word, and the number of output
bits is polynomial in the length of the input word (`Frontier.IsProjectionReduction`).
In particular they are computable by polynomial size circuits.

The circuit families witnessing membership in `NP` are not required to be uniformly
generated, so `Frontier.InNP` is the non-uniform version of `NP`; correspondingly the
reductions produced by the hardness proof are non-uniform (but they are projections,
which is a much more restrictive class than polynomial time computable maps).
-/

namespace Frontier

/-- `L₁` reduces to `L₂` by a projection reduction. -/

theorem red_spec (V : NPVerifier L) (x : List Bool) :
    (∃ a : ℕ → Bool, CNF.eval a (PCnf.inst x (redP V x.length)) = true) ↔ x ∈ L := by
  set n := x.length with hn
  set m := V.wlen n with hm
  set gs := V.circ n with hgs
  set fixed := modeVal (redMode V n) x with hfixed
  have hfix : ∀ i, fixed i =
      if i < n then some (x.getD i false) else if i < n + m then none else some false := by
    intro i
    simp only [hfixed, modeVal, redMode, ← hm]
    split
    · simp [ProjBit.eval]
    · split <;> simp [ProjBit.eval]
  rw [inst_redP, V.spec x, ← hn, ← hm, ← hgs]
  by_cases hlen : gs.length = 0
  · have hgsnil : gs = [] := List.eq_nil_of_length_eq_zero hlen
    constructor
    · rintro ⟨a, ha⟩
      rw [if_pos hlen, hgsnil] at ha
      simp only [tseitin, List.zipIdx_nil, List.flatMap_nil, List.nil_append] at ha
      simp [CNF.eval, CNF.Clause.eval] at ha
    · rintro ⟨w, _, hw⟩
      rw [hgsnil, circ_eval_nil] at hw
      exact absurd hw (by simp)
  · rw [if_neg hlen]
    constructor
    · rintro ⟨a, ha⟩
      rw [CNF.eval_append] at ha
      have ha1 : CNF.eval a (tseitin fixed gs) = true := by
        revert ha; cases CNF.eval a (tseitin fixed gs) <;> simp
      have ha2 : a (gv (gs.length - 1)) = true := by
        have : CNF.eval a [[(gv (gs.length - 1), true)]] = true := by
          revert ha; cases CNF.eval a [[(gv (gs.length - 1), true)]] <;> simp
        simpa [CNF.eval, CNF.Clause.eval] using this
      set X := inputOf fixed a with hX
      have hsound := tseitin_sound (V.wf n) ha1
      rw [← hgs] at hsound
      have hacc : Circ.eval gs X = true := by
        rw [Circ.eval, ← hsound (gs.length - 1) (by omega)]
        exact ha2
      refine ⟨(List.range m).map (fun i => X (n + i)), by simp, ?_⟩
      have hassign : assign x ((List.range m).map (fun i => X (n + i))) = X := by
        funext i
        rcases lt_or_ge i n with hi | hi
        · simp only [assign, ← hn, if_pos hi]
          rw [hX, inputOf, hfix i, if_pos hi]
          simp
        · rcases lt_or_ge i (n + m) with hi2 | hi2
          · have hidx : i - n < m := by omega
            simp only [assign, ← hn]
            rw [if_neg (show ¬ i < n by omega)]
            rw [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_range (by simpa using hidx)]
            simp only [Option.map_some, Option.getD_some]
            congr 1
            omega
          · simp only [assign, ← hn]
            rw [if_neg (show ¬ i < n by omega)]
            rw [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_none (l := List.range m) (by simp; omega)]
            rw [hX, inputOf, hfix i, if_neg (by omega), if_neg (by omega)]
            simp
      rw [hassign]
      exact hacc
    · rintro ⟨w, hwlen, hw⟩
      set X := assign x w with hXdef
      have hx : ∀ i b, fixed i = some b → X i = b := by
        intro i b hib
        rw [hfix i] at hib
        rcases lt_or_ge i n with hi | hi
        · rw [if_pos hi] at hib
          have : b = x.getD i false := by simpa using hib.symm
          rw [this, hXdef, assign, if_pos (by omega)]
        · rw [if_neg (by omega)] at hib
          rcases lt_or_ge i (n + m) with hi2 | hi2
          · rw [if_pos hi2] at hib; exact absurd hib (by simp)
          · rw [if_neg (by omega)] at hib
            have hb : b = false := by simpa using hib.symm
            rw [hb, hXdef, assign, if_neg (by omega)]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            simp
      refine ⟨assignOf gs X, ?_⟩
      rw [CNF.eval_append]
      have h1 : CNF.eval (assignOf gs X) (tseitin fixed gs) = true :=
        tseitin_complete (V.wf n) hx
      have h2 : CNF.eval (assignOf gs X) [[(gv (gs.length - 1), true)]] = true := by
        have hval : assignOf gs X (gv (gs.length - 1)) = true := by
          rw [assignOf_gv]; exact hw
        simp [CNF.eval, CNF.Clause.eval, hval]
      rw [h1, h2]
      rfl

/-- The reduction is correct. -/
