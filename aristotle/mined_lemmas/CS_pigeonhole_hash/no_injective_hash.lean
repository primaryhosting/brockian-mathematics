import Mathlib
import RequestProject.Main

/-!
# Pigeonhole Hash — generalisation to arbitrary finite types

A Mathlib-based restatement of `CS.pigeonhole_hash` for arbitrary finite key and value
types, derived from the core-library version proved in `RequestProject/Main.lean`.
-/

namespace CS

/-- Any hash function from a set of `n + 1` keys to a set of `n` hash values has a
collision. -/

theorem no_injective_hash (n : Nat) (f : Fin (n + 1) → Fin n) :
    ¬ (∀ a b : Fin (n + 1), f a = f b → a = b) := by
  intro hinj
  obtain ⟨a, b, hab, hfab⟩ := pigeonhole_hash n f
  exact hab (hinj a b hfab)

end CS

