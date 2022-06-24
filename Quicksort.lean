import Mathlib

def partition (A : List ℕ) (lo : ℤ) (hi : ℕ) : ℕ × List ℕ :=
  let pivot := A[hi]
  let i := lo - 1
  do

def quick (A : List ℕ) (lo : ℤ) (hi : ℕ) : List ℕ :=
  if lo ≥ hi || lo < 0 then A else
    let (p, B) := partition A lo hi
    let left := quick B lo p - 1
    let right := quick B p hi
    left ++ right


#eval quick [3, 2, 1] (-1) 0
#eval quick [3, 2, 1] 1 0
#eval quick [3, 2, 1] 0 2

def quick2 : List ℤ → List ℤ
| [] => []
| List.cons x xs =>
  have first_half_terminates : List.length (List.filter (fun y => decide (y < x)) xs) < Nat.succ (List.length xs) := by
    rw [List.filter, List.filterAux]
    sorry
  have first_half_terminates : List.length (List.filter (fun y => decide (y ≥ x)) xs) < Nat.succ (List.length xs) :=
    sorry
  quick2 (List.filter (λ y => y < x) xs) ++ x :: (quick2 (List.filter (λ y => y ≥ x) xs))
termination_by quick2 xs => xs.length
