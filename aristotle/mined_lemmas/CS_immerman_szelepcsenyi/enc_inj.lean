import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


lemma enc_inj : Function.Injective (enc (m := m)) := by
  intro a b h
  cases a <;> cases b <;>
    simp only [enc, Prod.mk.injEq] at h <;>
    (try exact absurd h.1 (by decide)) <;>
    obtain ⟨-, h⟩ := h <;>
    simp_all [vtx, Fin.ext_iff]

noncomputable instance : Fintype (St m) := Fintype.ofInjective _ (enc_inj (m := m))

