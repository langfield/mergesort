import Mathlib
universe u

def filter (p : α → Bool) : List α → List α
  | [] => []
  | a::as => match p a with
    | true => a :: filter p as
    | false => filter p as

def quick2 : List ℤ → List ℤ
| [] => []
| List.cons x xs =>
  have first_half_terminates : List.length (filter (fun y => decide (y < x)) xs) < Nat.succ (List.length xs) := by
    induction xs
    rw [filter]
    simp_all_arith
    rename_i ih
    rename_i tail
    rename_i head
    rw [filter]
    cases tail
    split
    simp_all_arith
    simp_all_arith
    split
    rename_i order
    rename_i my_bool
    rename_i tail
    rename_i head
    rename_i second_head
    rw [List.length]
    simp_all_arith
    rename_i head_not_lt_x
    rename_i bool
    rename_i tail
    rename_i second_head
    simp at ih
    simp_all_arith
    apply @le_trans ℤ 








  have first_half_terminates : List.length (filter (fun y => decide (y ≥ x)) xs) < Nat.succ (List.length xs) :=
    sorry
  quick2 (filter (λ y => y < x) xs) ++ x :: (quick2 (filter (λ y => y ≥ x) xs))
termination_by quick2 xs => xs.length
