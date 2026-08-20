/-
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- The diagonal partial function built from a candidate halting decider `H`:
on input `n` it loops forever if `H` says that the `n`-th program halts on input `n`,
and returns `0` otherwise. -/
noncomputable def diag (H : Code → ℕ → Bool) : ℕ →. ℕ := fun n =>
  Nat.rfind fun _ => Part.some (!H (Denumerable.ofNat Code n) n)

/-- Domain of an `rfind` over a constant predicate. -/
theorem rfind_const_dom (b : Bool) : (Nat.rfind fun _ => Part.some b).Dom ↔ b = true := by
  constructor
  · intro h
    have := Nat.rfind_spec (Part.get_mem h)
    simpa using this
  · intro h
    obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun _ => b) (m := 0) (by simp [h])
    exact Part.dom_iff_mem.2 ⟨n, hn⟩

theorem diag_dom (H : Code → ℕ → Bool) (n : ℕ) :
    (diag H n).Dom ↔ H (Denumerable.ofNat Code n) n = false := by
  rw [diag, rfind_const_dom]
  simp

theorem partrec_diag {H : Code → ℕ → Bool} (hH : Computable₂ H) : Nat.Partrec (diag H) := by
  have hc : Computable fun p : ℕ × ℕ => !H (Denumerable.ofNat Code p.1) p.1 :=
    (Primrec.not.to_comp).comp
      (hH.comp ((Computable.ofNat Code).comp Computable.fst) Computable.fst)
  have : Partrec (fun n : ℕ => Nat.rfind fun _ => Part.some (!H (Denumerable.ofNat Code n) n)) :=
    Partrec.rfind (p := fun n _ : ℕ => (Part.some (!H (Denumerable.ofNat Code n) n) : Part Bool))
      (Computable₂.partrec₂ (f := fun n _ : ℕ => !H (Denumerable.ofNat Code n) n) hc)
  exact Partrec.nat_iff.mp this

/-- **The halting problem is undecidable.**

There is no total computable function `H` which, given (a code for) a program `c` and an
input `x`, decides whether `c` halts on `x`.  The proof is by diagonalization: from such an
`H` one builds a partial recursive function that halts on the index `n` of a program exactly
when `H` claims that program does *not* halt on `n`, and applies it to its own index. -/
theorem halting_undecidable :
    ¬ ∃ H : Code → ℕ → Bool, Computable₂ H ∧ ∀ (c : Code) (x : ℕ), H c x = true ↔ (eval c x).Dom := by
  rintro ⟨H, hH, hspec⟩
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (partrec_diag hH)
  set n : ℕ := Encodable.encode c with hn
  have hoc : Denumerable.ofNat Code n = c := by
    simp [hn, Denumerable.ofNat_encode]
  have h1 : (eval c n).Dom ↔ H c n = false := by
    rw [hc]
    simpa [hoc] using diag_dom H n
  have h2 : H c n = true ↔ (eval c n).Dom := hspec c n
  rcases hb : H c n with _ | _
  · exact absurd (h2.mpr (h1.mpr hb)) (by simp [hb])
  · simp [hb] at h1
    exact absurd (h1 (h2.mp hb)) (by simp)

/-- The single-input form: for each fixed input `n`, the set of programs halting on `n`
is not a computable predicate. -/
theorem halting_undecidable_fixed_input (n : ℕ) :
    ¬ ComputablePred fun c : Code => (eval c n).Dom :=
  ComputablePred.halting_problem n

end CS

