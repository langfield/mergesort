import Mathlib

#check List.filterAux

def filterAux (p : α → Bool) : List α → List α → List α
  | [],    rs => rs.reverse
  | a::as, rs => match p a with
     | true  => filterAux p as (a::rs)
     | false => filterAux p as rs

@[inline] def filter (p : α → Bool) (as : List α) : List α :=
  filterAux p as []

def quick2 : List ℤ → List ℤ
| [] => []
| List.cons x xs =>
  have first_half_terminates : List.length (filter (fun y => decide (y < x)) xs) < Nat.succ (List.length xs) := by
    rw [filter]
    sorry
  have first_half_terminates : List.length (filter (fun y => decide (y ≥ x)) xs) < Nat.succ (List.length xs) :=
    sorry
  quick2 (filter (λ y => y < x) xs) ++ x :: (quick2 (filter (λ y => y ≥ x) xs))
termination_by quick2 xs => xs.length
