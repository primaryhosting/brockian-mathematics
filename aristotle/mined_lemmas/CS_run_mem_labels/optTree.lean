import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree for sorting 4 elements.  A `node i j l r`
compares the keys at positions `i` and `j`, continuing in `l` if the key at `i`
is smaller and in `r` otherwise.  A `leaf p` announces that the input ordering
is the permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by a decision tree. -/

def optTree : DTree :=
  (CS.DTree.node 0 1
    (CS.DTree.node 0 2
      (CS.DTree.node 1 2
        (CS.DTree.node 1 3
          (CS.DTree.node 2 3
            (CS.DTree.leaf (CS.perm4 ![0,1,2,3] ![0,1,2,3] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![0,1,3,2] ![0,1,3,2] (by decide) (by decide))))
          (CS.DTree.node 0 3
            (CS.DTree.leaf (CS.perm4 ![0,2,3,1] ![0,3,1,2] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![1,2,3,0] ![3,0,1,2] (by decide) (by decide)))))
        (CS.DTree.node 2 3
          (CS.DTree.node 1 3
            (CS.DTree.leaf (CS.perm4 ![0,2,1,3] ![0,2,1,3] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![0,3,1,2] ![0,2,3,1] (by decide) (by decide))))
          (CS.DTree.node 0 3
            (CS.DTree.leaf (CS.perm4 ![0,3,2,1] ![0,3,2,1] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![1,3,2,0] ![3,0,2,1] (by decide) (by decide))))))
      (CS.DTree.node 0 3
        (CS.DTree.node 1 3
          (CS.DTree.leaf (CS.perm4 ![1,2,0,3] ![2,0,1,3] (by decide) (by decide)))
          (CS.DTree.leaf (CS.perm4 ![1,3,0,2] ![2,0,3,1] (by decide) (by decide))))
        (CS.DTree.node 2 3
          (CS.DTree.leaf (CS.perm4 ![2,3,0,1] ![2,3,0,1] (by decide) (by decide)))
          (CS.DTree.leaf (CS.perm4 ![2,3,1,0] ![3,2,0,1] (by decide) (by decide))))))
    (CS.DTree.node 0 2
      (CS.DTree.node 0 3
        (CS.DTree.node 2 3
          (CS.DTree.leaf (CS.perm4 ![1,0,2,3] ![1,0,2,3] (by decide) (by decide)))
          (CS.DTree.leaf (CS.perm4 ![1,0,3,2] ![1,0,3,2] (by decide) (by decide))))
        (CS.DTree.node 1 3
          (CS.DTree.leaf (CS.perm4 ![2,0,3,1] ![1,3,0,2] (by decide) (by decide)))
          (CS.DTree.leaf (CS.perm4 ![2,1,3,0] ![3,1,0,2] (by decide) (by decide)))))
      (CS.DTree.node 1 2
        (CS.DTree.node 2 3
          (CS.DTree.node 0 3
            (CS.DTree.leaf (CS.perm4 ![2,0,1,3] ![1,2,0,3] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![3,0,1,2] ![1,2,3,0] (by decide) (by decide))))
          (CS.DTree.node 1 3
            (CS.DTree.leaf (CS.perm4 ![3,0,2,1] ![1,3,2,0] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![3,1,2,0] ![3,1,2,0] (by decide) (by decide)))))
        (CS.DTree.node 1 3
          (CS.DTree.node 0 3
            (CS.DTree.leaf (CS.perm4 ![2,1,0,3] ![2,1,0,3] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![3,1,0,2] ![2,1,3,0] (by decide) (by decide))))
          (CS.DTree.node 2 3
            (CS.DTree.leaf (CS.perm4 ![3,2,0,1] ![2,3,1,0] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![3,2,1,0] ![3,2,1,0] (by decide) (by decide))))))))

