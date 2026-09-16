import Mathlib

/-!
# Observer-relative holonomy

The observable invariant of a labelled loop translation is the image of its
holonomy in the observer's quotient. Intermediate quotients are allowed.
This file proves the observer and loop-return statements for arbitrary moduli.
The determinant of the one-step seam permutation is a separate obligation,
recorded as a `Prop` below, not asserted as a proved theorem.
-/

namespace Brockian.HolonomyObservers

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

def loop (h : A) (x : A) : A := x + h

theorem loop_iterate (h x : A) (n : ℕ) : (loop h)^[n] x = x + n • h := by
  induction n generalizing x with
  | zero => simp [loop]
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp [loop, succ_nsmul, add_assoc, add_left_comm, add_comm]

theorem observe_loop (π : A →+ B) (h x : A) : π (loop h x) = π x + π h :=
  π.map_add x h

theorem observer_equivalence (π : A →+ B) (h k : A) :
    (∀ x, π (loop h x) = π (loop k x)) ↔ π h = π k := by
  constructor
  · intro heq
    simpa [loop] using heq 0
  · intro heq x
    simp only [observe_loop, heq]

theorem observer_kernel (π : A →+ B) (h k : A) :
    (∀ x, π (loop h x) = π (loop k x)) ↔ h - k ∈ π.ker := by
  rw [observer_equivalence]
  simp only [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]

theorem labelled_observer (h k : A) :
    (∀ x, loop h x = loop k x) ↔ h = k := by
  simpa using observer_equivalence (AddMonoidHom.id A) h k

theorem coarsening_preserves_indistinguishability
    (π : A →+ B) (ψ : B →+ C) (h k : A)
    (heq : ∀ x, π (loop h x) = π (loop k x)) :
    ∀ x, (ψ.comp π) (loop h x) = (ψ.comp π) (loop k x) := by
  intro x
  exact congrArg ψ (heq x)

/-- The same fact applies to any number of completed loops. -/
theorem observe_loops (π : A →+ B) (h x : A) (n : ℕ) :
    π ((loop h)^[n] x) = π x + n • π h := by
  rw [loop_iterate, map_add, map_nsmul]

theorem loop_return_iff {m : ℕ} [NeZero m] (h : ℕ) (x : ZMod m) (n : ℕ) :
    (loop (h : ZMod m))^[n] x = x ↔ m / m.gcd h ∣ n := by
  rw [loop_iterate]
  have hzero : x + n • (h : ZMod m) = x ↔ n • (h : ZMod m) = 0 := by
    exact add_eq_left
  rw [hzero, ← addOrderOf_dvd_iff_nsmul_eq_zero,
    ZMod.addOrderOf_coe h (NeZero.ne m)]

def modFour : ZMod 8 →+ ZMod 4 :=
  (ZMod.castHom (show 4 ∣ 8 by decide) (ZMod 4)).toAddMonoidHom

/-- An explicit intermediate observer: it identifies 1 and 5, but separates 1 and 3. -/
theorem intermediate_observer :
    modFour 1 = modFour 5 ∧ modFour 1 ≠ modFour 3 ∧ (1 : ZMod 8) ≠ 5 := by
  decide

def combinedObserver (h : ZMod 8) : ℕ × ZMod 4 := (8.gcd h.val, modFour h)

/-- Combining the determinant invariant and a quotient gives a strict
intermediate observer between gcd alone and the fully labelled holonomy. -/
theorem combined_observer_strict :
    (8.gcd (1 : ZMod 8).val = 8.gcd (3 : ZMod 8).val) ∧
    combinedObserver 1 ≠ combinedObserver 3 ∧
    combinedObserver 1 = combinedObserver 5 ∧ (1 : ZMod 8) ≠ 5 := by
  decide

theorem combined_observer_refines_gcd (h k : ZMod 8)
    (heq : combinedObserver h = combinedObserver k) : 8.gcd h.val = 8.gcd k.val :=
  congrArg Prod.fst heq

def seamStep (q m : ℕ) [NeZero q] (h : ZMod m)
    (x : ZMod q × ZMod m) : ZMod q × ZMod m :=
  (x.1 + 1, x.2 + if x.1 = -1 then h else 0)

theorem residue_observer_independent (q m : ℕ) [NeZero q]
    (h k : ZMod m) (x : ZMod q × ZMod m) :
    (seamStep q m h x).1 = (seamStep q m k x).1 := rfl

def seamMatrix (q m : ℕ) [NeZero q] [NeZero m] (h : ZMod m) :
    Matrix (ZMod q × ZMod m) (ZMod q × ZMod m) ℚ :=
  Matrix.of fun i j => if seamStep q m h j = i then 1 else 0

/-- Target of the remaining cycle-decomposition formalization. Merely defining
this proposition does not prove it. The written proof is in the review notes. -/
def SeamDeterminantStatement (q m h : ℕ) [NeZero q] [NeZero m] : Prop :=
  ∀ z : ℚ,
    Matrix.det (1 - z • seamMatrix q m (h : ZMod m)) =
    (1 - z ^ (q * (m / m.gcd h))) ^ m.gcd h

end Brockian.HolonomyObservers
