import Mathlib

#check List.filterAux

def quick2 : List ℤ → List ℤ
| [] => []
| List.cons x xs =>
  have first_half_terminates : List.length (List.filter (fun y => decide (y < x)) xs) < Nat.succ (List.length xs) := by
    rw [List.filter]
    cases xs
    · rw [List.filterAux]
      rw [List.reverse] 
      rw [List.reverseAux]
      rw [List.length]
      rw [Nat.succ_eq_add_one, Nat.zero_add]
      simp
    · unfold List.filterAux
      rename_i head tail
      simp_arith
      split


      
  have first_half_terminates : List.length (List.filter (fun y => decide (y ≥ x)) xs) < Nat.succ (List.length xs) :=
    sorry
  quick2 (List.filter (λ y => y < x) xs) ++ x :: (quick2 (List.filter (λ y => y ≥ x) xs))
termination_by quick2 xs => xs.length
