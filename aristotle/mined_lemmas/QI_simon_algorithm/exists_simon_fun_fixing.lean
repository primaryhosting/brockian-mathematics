/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

lemma exists_simon_fun_fixing (s : Bits n) (hs : s ≠ 0) (Q : Finset (Bits n))
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x + y ≠ s) :
    ∃ g : Bits n → Bits n, SimonPromise g s ∧ ∀ x ∈ Q, g x = x := by
  classical
  obtain ⟨j, hj0⟩ : ∃ j, s j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs (funext h)
  have hj : s j = 1 := by
    rcases zmod_two_cases (s j) with h | h
    · exact absurd h hj0
    · exact h
  set r : Bits n → Bits n := rep s j with hr
  have hrinj : ∀ x ∈ Q, ∀ y ∈ Q, r x = r y → x = y := by
    intro x hx y hy hxy
    rcases (rep_eq_iff s j hj x y).1 hxy with h | h
    · exact h.symm
    · exfalso
      apply hQ x hx y hy
      rw [h, ← add_assoc, bits_add_self, zero_add]
  set R : Finset (Bits n) := Q.image r with hR
  have hphi : Function.Bijective (fun x : {x // x ∈ Q} => (⟨r x.1, by
      rw [hR]; exact Finset.mem_image_of_mem r x.2⟩ : {z // z ∈ R})) := by
    constructor
    · intro a b hab
      have : r a.1 = r b.1 := congrArg Subtype.val hab
      exact Subtype.ext (hrinj a.1 a.2 b.1 b.2 this)
    · rintro ⟨z, hz⟩
      rw [hR, Finset.mem_image] at hz
      obtain ⟨x, hx, hxz⟩ := hz
      exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  set e : {z // z ∈ R} ≃ {x // x ∈ Q} := (Equiv.ofBijective _ hphi).symm with he
  set sigma : Equiv.Perm (Bits n) := Equiv.extendSubtype e with hsigma
  refine ⟨fun x => sigma (r x), ⟨hs, ?_⟩, ?_⟩
  · intro x y
    show sigma (r x) = sigma (r y) ↔ (y = x ∨ y = x + s)
    constructor
    · intro h
      have : r x = r y := sigma.injective h
      exact (rep_eq_iff s j hj x y).1 this
    · intro h
      have hrr : r x = r y := (rep_eq_iff s j hj x y).2 h
      rw [hrr]
  · intro x hx
    show sigma (r x) = x
    have hmem : r x ∈ R := by rw [hR]; exact Finset.mem_image_of_mem r hx
    have h1 : sigma (r x) = (e ⟨r x, hmem⟩ : Bits n) := Equiv.extendSubtype_apply_of_mem e _ hmem
    rw [h1, he]
    have : (Equiv.ofBijective _ hphi) ⟨x, hx⟩ = ⟨r x, hmem⟩ := rfl
    rw [← this, Equiv.symm_apply_apply]

end Construction

/-- **Classical lower bound.**  Any deterministic classical algorithm that solves Simon's
problem on `n` bits with `q` queries satisfies `2^n ≤ q^2 + 2`. -/
