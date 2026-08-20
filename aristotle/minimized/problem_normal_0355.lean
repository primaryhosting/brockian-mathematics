import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0355 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ z) ◇ (z ◇ z)))
    : ∀ (x : G) (y : G), (x ◇ x) ◇ x = (y ◇ y) ◇ y := by
  have hall : ∀ a b : G, a = b := by
    intro a b
    have h1 := h a b a; have h2 := h b a b
    have h3 := h a a a; have h6 := h b b b
    have h4 := h ((a◇a)◇(a◇a)) a ((b◇b)◇(b◇b))
    have h5 := h ((b◇b)◇(b◇b)) b ((a◇a)◇(a◇a))
    grind
  intro x y; exact hall _ _

-- Problem normal_0362: eq409 → eq4659
