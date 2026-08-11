import Mathlib

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

open Nat.Partrec Nat.Partrec.Code

/-- The diagonal partial function: on input `n` it halts (returning `0`) exactly when
`H n n = false`, and diverges otherwise. It is partial recursive whenever `H` is computable. -/
noncomputable def diag (H : ℕ → ℕ → Bool) : ℕ →. ℕ :=
  fun n => Nat.rfind fun _ => Part.some (!(H n n))

theorem diag_partrec {H : ℕ → ℕ → Bool} (hH : Computable₂ H) : Nat.Partrec (diag H) := by
  refine Partrec.nat_iff.1 (Partrec.rfind ?_)
  exact ((((Primrec.dom_bool (fun b => !b)).to_comp.comp
    (hH.comp Computable.id Computable.id))).comp Computable.fst).partrec

/-- The diagonal function halts on `n` iff `H n n = false`. -/
theorem diag_dom_iff (H : ℕ → ℕ → Bool) (n : ℕ) : (diag H n).Dom ↔ H n n = false := by
  constructor
  · intro h
    have := Nat.rfind_spec (Part.get_mem h)
    simpa using this
  · intro h
    have : (0 : ℕ) ∈ diag H n := by
      rw [diag, Nat.mem_rfind]
      simp [h]
    exact this.fst

/-- **Undecidability of the halting problem** (by diagonalization).

There is no total computable function `H` which, given (a code for) a program `c` and an
input `x`, decides whether the program `c` halts on input `x`. -/
theorem halting_undecidable :
    ¬ ∃ H : ℕ → ℕ → Bool, Computable₂ H ∧
        ∀ (c : Nat.Partrec.Code) (x : ℕ),
          H (Encodable.encode c) x = true ↔ (Nat.Partrec.Code.eval c x).Dom := by
  rintro ⟨H, hH, hspec⟩
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (diag_partrec hH)
  set n : ℕ := Encodable.encode c
  have h1 : (Nat.Partrec.Code.eval c n).Dom ↔ H n n = false := by
    rw [hc]; exact diag_dom_iff H n
  have h2 : H n n = true ↔ (Nat.Partrec.Code.eval c n).Dom := hspec c n
  cases hb : H n n with
  | false =>
      have h3 : H n n = true := h2.2 (h1.2 hb)
      rw [hb] at h3
      exact Bool.false_ne_true h3
  | true =>
      have : H n n = false := h1.1 (h2.1 hb)
      simp [hb] at this

end CS

