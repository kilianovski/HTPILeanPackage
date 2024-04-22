import Mathlib.Data.Set.Basic
import Mathlib


example {R : Type*} [Field R] :
    {(x, y) | (x : R) (y : R) (h : y = 2 * x - 3)} = { (x, 2 * x - 3) | x : R} := by





variable (U: Type)
variable (A: Set U) (B: Set U) (C: Set U)
variable (ValidSet: A × B)



#check A
#check ValidSet
variable (C: A × (B ∩ C))



theorem Theorem_4_1_3_1 {U : Type}
    (A : Set U) (B: Set U) (C: Set U) (D: Set U) :
      (((B ∩ C)) = (A × B) ∩ (A × C)):= sorry
