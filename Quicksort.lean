import Mathlib
universe u

def filter (p : α → Bool) : List α → List α
  | [] => []
  | a::as => match p a with
    | true => a :: filter p as
    | false => filter p as

def half_terminates (xs : List ℤ) (decider : ℤ → Bool) : List.length (filter decider xs) < Nat.succ (List.length xs) := by
  induction xs
  rw [filter]
  simp_all_arith
  rename_i ih
  rename_i tail
  rw [filter]
  cases tail
  split
  simp_all_arith
  simp_all_arith
  split
  simp_all_arith
  apply le_trans ih
  simp_all_arith

-- Quicksort in Lean 4.
def quick2 : List ℤ → List ℤ
| []      => []
| x :: xs =>
  -- Helper proofs for termination-checking.
  have _ : List.length (filter (fun y => decide (y < x)) xs) < Nat.succ (List.length xs) :=
    half_terminates xs (fun y => decide (y < x))
  have _ : List.length (filter (fun y => decide (y ≥ x)) xs) < Nat.succ (List.length xs) :=
    half_terminates xs (fun y => decide (y ≥ x))
  quick2 (filter (λ y => y < x) xs) ++ x :: (quick2 (filter (λ y => y ≥ x) xs))
termination_by quick2 xs => xs.length

#eval quick2 [1,2,3]
#eval quick2 [3,2,1]
#eval quick2 [3,1,2]
#eval quick2 [1]
