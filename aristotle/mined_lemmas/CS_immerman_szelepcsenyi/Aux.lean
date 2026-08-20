import RequestProject.Counting

/-!
# Soundness of the counting machine

We define an invariant of the states of the counting machine which is satisfied by the
initial state and preserved by every transition, and which guarantees, in the accepting
phase, that no accepting vertex is reachable.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable (G : Data) (x : List Bool)

/-- The invariant of the inner loop: the vertices counted so far form a set `S` of vertices
`< u` reachable in `i` steps, and the flag correctly records whether one of them witnesses
the reachability of `v` in `i+1` steps. -/

lemma Aux.enc_injective {N : ℕ} : Function.Injective (Aux.enc (N := N)) := by
  rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ h
  simp only [Aux.enc, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; subst h8; subst h9
  subst h10; rfl

noncomputable instance {N : ℕ} : Fintype (Aux N) := Fintype.ofInjective _ Aux.enc_injective

