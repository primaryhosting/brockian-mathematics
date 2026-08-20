

theorem test (a b c : Nat) (h : a = b) (h2 : b = c) : a = c := by grind

import Mathlib.Tactic

set_option quotPrecheck false

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

set_option maxHeartbeats 1600000

