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

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem diophFn_apProd {f g h : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g)
    (dh : DiophFn h) : DiophFn fun v => apProd (f v) (g v) (h v) := by
  set F : (Option α → ℕ) → ℕ := fun w => f (w ∘ some) with hF
  set G : (Option α → ℕ) → ℕ := fun w => g (w ∘ some) with hG
  set H : (Option α → ℕ) → ℕ := fun w => h (w ∘ some) with hH
  set Y : (Option α → ℕ) → ℕ := fun w => w none with hY
  have dF : DiophFn F := diophFn_lift df
  have dG : DiophFn G := diophFn_lift dg
  have dH : DiophFn H := diophFn_lift dh
  have dY : DiophFn Y := diophFn_head
  set M : (Option α → ℕ) → ℕ := fun w => G w * (F w + H w * G w) ^ H w + 1 with hM
  have dM : DiophFn M :=
    diophFn_add (diophFn_mul dG (diophFn_pow (diophFn_add dF (diophFn_mul dH dG)) dH))
      (diophFn_const 1)
  -- the existential part
  have dex : Dioph {w : Option α → ℕ | ∃ c,
      (G w * c) % M w = F w % M w ∧
        Y w % M w = (G w ^ H w * ((H w).factorial * (c + H w).choose (H w))) % M w} := by
    refine dioph_ex ?_
    have dc : DiophFn (fun w' : Option (Option α) → ℕ => w' none) := diophFn_head
    have dF' : DiophFn (fun w' : Option (Option α) → ℕ => F (w' ∘ some)) := diophFn_lift dF
    have dG' : DiophFn (fun w' : Option (Option α) → ℕ => G (w' ∘ some)) := diophFn_lift dG
    have dH' : DiophFn (fun w' : Option (Option α) → ℕ => H (w' ∘ some)) := diophFn_lift dH
    have dY' : DiophFn (fun w' : Option (Option α) → ℕ => Y (w' ∘ some)) := diophFn_lift dY
    have dM' : DiophFn (fun w' : Option (Option α) → ℕ => M (w' ∘ some)) := diophFn_lift dM
    exact dioph_and (dioph_eq (diophFn_mod (diophFn_mul dG' dc) dM') (diophFn_mod dF' dM'))
      (dioph_eq (diophFn_mod dY' dM')
        (diophFn_mod (diophFn_mul (diophFn_pow dG' dH')
          (diophFn_mul (diophFn_factorial dH') (diophFn_choose (diophFn_add dc dH') dH'))) dM'))
  have dT : Dioph {w : Option α → ℕ | (G w = 0 ∧ Y w = F w ^ H w) ∨
      (1 ≤ G w ∧ Y w < M w ∧ ∃ c,
        (G w * c) % M w = F w % M w ∧
        Y w % M w = (G w ^ H w * ((H w).factorial * (c + H w).choose (H w))) % M w)} :=
    dioph_or (dioph_and (dioph_eq dG (diophFn_const 0)) (dioph_eq dY (diophFn_pow dF dH)))
      (dioph_and (dioph_le (diophFn_const 1) dG) (dioph_and (dioph_lt dY dM) dex))
  refine Dioph.ext dT fun w => ?_
  constructor
  · intro hw
    exact ((apProd_spec (F w) (G w) (H w) (Y w)).2 hw).symm
  · intro hw
    exact (apProd_spec (F w) (G w) (H w) (Y w)).1 hw.symm

end H10

/-
Auxiliary facts about the integer polynomials underlying Mathlib's `Dioph` predicate:

* a polynomial depends on only finitely many variables, and is bounded by
  `C * (B+1)^d` on arguments bounded by `B`;
* polynomials respect congruences;
* every Diophantine set can be described with only finitely many auxiliary variables.
-/
import RequestProject.H10.Basic

open Dioph

namespace H10

variable {γ δ α : Type}

/-- A polynomial depends on only finitely many of its variables, and is bounded by
`C * (B+1)^d` on arguments bounded by `B`. -/
