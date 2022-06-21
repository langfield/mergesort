import Mathlib

def merge : List Nat → List Nat → List Nat
| xs, [] => xs
| [], ys => ys
| (x :: xs), (y :: ys) => if x < y then x :: (merge xs ( y :: ys))
                                   else y :: (merge (x :: xs) ys)
termination_by merge xs ys => xs.length + ys.length

def first_half {α : Type} (xs : List α) : List α := 
  List.take (xs.length / 2) xs

def second_half {α : Type} (xs : List α) : List α :=
  List.drop (xs.length / 2) xs

def half_add_one_lt_add_two (n : Nat) : n / 2 + 1 < n + 2 := by
  induction n with
  | zero => simp
  | succ m h =>
    rw [Nat.succ_eq_add_one]
    have zero_lt_m_add_one : 0 < m + 1 := by
      apply Nat.zero_lt_succ
    have one_lt_two : 1 < 2 := by simp
    have div_le_self := @Nat.div_lt_self (m + 1) 2 zero_lt_m_add_one one_lt_two
    apply Nat.succ_le_succ
    apply Nat.succ_le_succ
    exact Nat.le_of_lt div_le_self

def one_add_one_eq_two : 1 + 1 = 2 := by simp

def mergesort : List Nat → List Nat
| [] => []
| [a] => [a]
| (x :: (y :: ys)) => 
  have : List.length (first_half (x :: (y :: ys))) < List.length (x :: (y :: ys)) := by
    rw [
      List.length_cons,
      List.length_cons,
      Nat.succ_eq_add_one,
      Nat.add_assoc,
      one_add_one_eq_two,
      first_half,
      List.length_cons,
      List.length_cons,
    ]
    simp
    rw [Nat.succ_eq_add_one, Nat.add_assoc, one_add_one_eq_two]
    simp
    rw [Nat.succ_eq_add_one]
    have half_lemma := half_add_one_lt_add_two (List.length ys)
    rw [min_eq_left]
    exact half_lemma
    exact Nat.le_of_lt half_lemma
  have : List.length (second_half (x :: (y :: ys))) < List.length (x :: (y :: ys)) := by
    rw [
      List.length_cons,
      List.length_cons,
      Nat.succ_eq_add_one,
      Nat.add_assoc,
      one_add_one_eq_two,
      second_half,
    ]
    simp
    rw [Nat.succ_eq_add_one, Nat.add_assoc, one_add_one_eq_two]
    simp
    rw [Nat.succ_eq_add_one]
    apply Nat.sub_lt_self
    rw [← Nat.succ_eq_add_one]
    exact Nat.zero_lt_succ (List.length ys / 2)
    apply Nat.le_of_lt
    apply half_add_one_lt_add_two
  merge (mergesort <| first_half (x :: (y :: ys))) (mergesort <| second_half (x :: (y :: ys)))
termination_by mergesort xs => xs.length

def l := [1, 2, 3]
#eval (l).length
#eval l.length
#eval l.take 1

#eval mergesort [1, 3, 2]
#eval mergesort [3, 2, 1]
