-- import Mathlib

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

theorem min_le_left (a b : ℕ) : Nat.min a b ≤ a := by
  simp [Nat.min]
  by_cases h : a ≤ b
  simp
  split
  simp
  simp
  split
  simp
  rw [Nat.not_le_eq] at h
  apply @Nat.le_trans b (b + 1) a
  simp
  exact Nat.le_succ b
  exact h

theorem min_eq_left (h : a ≤ b) : Nat.min a b = a := by simp [Nat.min, h]
theorem zero_min (a : ℕ) : Nat.min 0 a = 0 := min_eq_left (Nat.zero_le a)

theorem min_eq_right (h : b ≤ a) : Nat.min a b = b := by rw [Nat.min_comm a b]; exact min_eq_left h
theorem min_zero (a : ℕ) : min a 0 = 0 := min_eq_right (zero_le a)

@[simp] theorem length_take : ∀ (i : Nat) (l : List α), List.length (List.take i l) = Nat.min i (List.length l)
| 0, l => by
  simp [zero_min]
  rw [List.take]
  rw [List.length]
| Nat.succ n, [] => by simp [Nat.min_zero]
| Nat.succ n, a :: l => by simp [Nat.min_succ_succ, add_one, length_take]

-- theorem length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [min_le_left]
theorem length_take_le : List.length (List.take n l) ≤ n := by
  sorry
  
  
  

theorem nonempty_first_half_lt {x : ℕ} {xs : List ℕ} : List.length (first_half (x :: xs)) < List.length (x :: xs) := by
  rw [first_half]
  simp
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
    rw [first_half]
    rw [List.length_cons]
    rw [List.length_cons]
    simp
    rw [Nat.succ_eq_add_one]
    rw [Nat.add_assoc]
    rw [lem]
    simp
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
