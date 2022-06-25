import Mathlib
universe u

def quick2 : List ℤ → List ℤ
| [] => []
| List.cons x xs =>
  have first_half_terminates : List.length (List.filter (fun y => decide (y < x)) xs) < Nat.succ (List.length xs) := by
    rw [List.filter]
    induction xs
    repeat rw [List.filterAux, List.reverse, List.reverseAux]
    simp_all_arith
    rename_i ih
    rename_i tail
    rename_i head
    unfold List.filterAux
    split
    rename_i head_lt_x
    · simp_all_arith

      sorry
    · apply (lt_trans ih)
      simp_all_arith




  have first_half_terminates : List.length (List.filter (fun y => decide (y ≥ x)) xs) < Nat.succ (List.length xs) :=
    sorry
  quick2 (List.filter (λ y => y < x) xs) ++ x :: (quick2 (List.filter (λ y => y ≥ x) xs))
termination_by quick2 xs => xs.length
