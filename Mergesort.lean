import Mathlib.Init.Data.List.Lemmas
notation "ℕ" => Nat

def merge : List ℕ → List ℕ → List ℕ
| xs, [] => xs
| [], ys => ys
| (x :: xs), (y :: ys) => if x < y then x :: (merge xs ( y :: ys))
                                   else y :: (merge (x :: xs) ys)
termination_by merge xs ys => xs.length + ys.length

def first_half {α : Type} (xs : List α) : List α := 
  List.take (xs.length / 2) xs

def second_half {α : Type} (xs : List α) : List α :=
  List.drop (xs.length / 2) xs

theorem nonempty_first_half_lt {x : ℕ} {xs : List ℕ} : List.length (first_half (x :: xs)) < List.length (x :: xs) := by
  rw [first_half]
  simp
  let l1 := List.length_take_le (Nat.succ (List.length xs) / 2) (x :: xs)
  sorry

def mergesort : List ℕ → List ℕ
| [] => []
| [a] => [a]
| (x :: (y :: ys)) => 
  have : List.length (first_half (x :: (y :: ys))) < List.length (x :: (y :: ys)) := by
    rw [List.length_cons]
    rw [List.length_cons]
    rw [Nat.succ_eq_add_one]
    rw [Nat.add_assoc]
    simp
    let lem : 1 + 1 = 2 := by simp
    rw [lem]
    sorry
  have : List.length (second_half (x :: (y :: ys))) < List.length (x :: (y :: ys)) := by
    rw [List.length_cons]
    sorry
  merge (mergesort <| first_half (x :: (y :: ys))) (mergesort <| second_half (x :: (y :: ys)))
termination_by mergesort xs => xs.length

def l := [1, 2, 3]
#eval (l).length
#eval l.length
#eval l.take 1

#eval mergesort [1, 3, 2]
#eval mergesort [3, 2, 1]
