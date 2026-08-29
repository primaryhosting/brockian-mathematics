/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4

We show that the two-colour Ramsey number `R(4,4)` equals `18`:

* every symmetric two-colouring of the edges of the complete graph on `18` vertices
  contains a monochromatic set of `4` vertices;
* there is a symmetric two-colouring of the edges of the complete graph on `17` vertices
  (the Paley graph of order `17`) with no monochromatic set of `4` vertices.
-/

namespace Math

open Finset

/-- `MonoSet f b S` says that every pair of distinct vertices of `S` receives colour `b`. -/

lemma not_ramseyProp_of_le_17 {N : ℕ} (hN : N ≤ 17) : ¬ RamseyProp N := by
  intro h
  set g : Fin N → Fin 17 := Fin.castLE hN with hg
  have hginj : Function.Injective g := Fin.castLE_injective hN
  obtain ⟨S, hcard, hmono⟩ := h (fun i j => paleyColor (g i) (g j))
    (fun i j => paley_symm (g i) (g j))
  have hcard' : (S.image g).card = 4 := by
    rw [Finset.card_image_of_injective _ hginj, hcard]
  have himg : ∀ col : Bool, MonoSet (fun i j => paleyColor (g i) (g j)) col S →
      MonoSet paleyColor col (S.image g) := by
    intro col hm x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hm i hi j hj (fun hij => hxy (by rw [hij]))
  rcases hmono with hm | hm
  · exact paley_no_mono_finset hcard' true (himg true hm)
  · exact paley_no_mono_finset hcard' false (himg false hm)

/-- **The Ramsey number `R(4,4)` is `18`**: `18` is the least `N` such that every symmetric
two-colouring of the edges of the complete graph on `N` vertices contains a monochromatic
clique on `4` vertices. -/
