import Mathlib.Data.Matrix.Block

/-!
# Entrywise subtraction of block matrices
-/

namespace Matrix
variable {R m n p q : Type*}

/-- Subtraction acts independently on the four blocks. -/
theorem fromBlocks_sub [Sub R] (A A' : Matrix m p R) (B B' : Matrix m q R)
    (C C' : Matrix n p R) (D D' : Matrix n q R) :
    fromBlocks A B C D - fromBlocks A' B' C' D' =
      fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  cases i <;> cases j <;> rfl

end Matrix
