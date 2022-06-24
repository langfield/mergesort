import Mathlib
-- Credit to Alexander Bentkamp and Evgeniy Kuznetsov on the Lean zulip chat
-- for help cleaning up (really rewriting) these lemmas.

def merge : List Nat → List Nat → List Nat
| xs, [] => xs
| [], ys => ys
| (x :: xs), (y :: ys) => if x < y then x :: (merge xs (y :: ys))
                                   else y :: (merge (x :: xs) ys)
termination_by merge xs ys => xs.length + ys.length

-- When we (natural) divide the length of a list by 2, and the list has at
-- least 2 elements, then we get a number strictly smaller than the length of
-- the list.
lemma length_div_2 : List.length (x :: y :: ys) / 2 < List.length (x :: y :: ys) := by

  -- Let n be the length of the list, and k = 2.
  -- Then n / k < n when 1 < k and 0 < n.
  apply Nat.div_lt_self

  -- So now we must prove 1 < k and 0 < n.
  -- We do the latter first.
  · simp [Nat.zero_lt_succ]

  -- And then we prove 1 < k.
  · simp

lemma length_sub_div_2 : List.length (x :: y :: ys) - List.length (x :: y :: ys) / 2 < List.length (x :: y :: ys) := by

  -- Let `b` be the length of the list, and `a` be half the length of the list.
  -- If 0 < a and a ≤ b, then b - a < b.
  apply Nat.sub_lt_self

  -- Now we prove 0 < a.
  -- If n + 1 ≤ m, then n < m.
  apply Nat.lt_of_succ_le

  -- Multiply both sides of an `≤` by k (in this case, 2).
  rw [Nat.le_div_iff_mul_le]

  -- Simplify Nat.succ 0 * 2 → 2.
  simp only [Nat.succ_eq_one_add, Nat.add_zero, Nat.one_mul]

  -- Prove that 2 ≤ length of a list with length at least 2.
  simp only [Nat.succ_eq_one_add, ← add_assoc, Nat.le_add_right, List.length_cons]

  -- Show 0 < 2. 
  apply Nat.zero_lt_succ

  -- Now our goal is basically exactly the statement of `length_div_2`.
  -- Since `length_div_2` is for `<`, convert it to `≤`.
  exact le_of_lt length_div_2

def first_half {α : Type} (xs : List α) : List α := 
  List.take (xs.length / 2) xs

def second_half {α : Type} (xs : List α) : List α :=
  List.drop (xs.length / 2) xs

lemma length_first_half : List.length (first_half (x :: y :: ys)) < List.length (x :: y :: ys) := by
  -- Use the definition of `first_half`, and the theorem that says that if we
  -- take `i` values from the beginning of a list, we'll get either `i` values
  -- or the entire list, whichever is smaller.
  -- 
  -- Then use the theorem that says that min(a, b) is `a` if a < b.
  -- Note that in our case, `b` is the length, and `a`is the length divided by
  -- two.
  rw [first_half, List.length_take, min_eq_left_of_lt]
  repeat exact length_div_2
  
lemma length_second_half : List.length (second_half (x :: y :: ys)) < List.length (x :: y :: ys) := by
  -- Use the definition of `second_half`, and then the theorem that says that
  -- after we drop the first `i` values from a list, the result has length
  -- `length - i` (natural subtraction).
  rw [second_half, List.length_drop]
  repeat exact length_sub_div_2

def mergesort : List Nat → List Nat
| [] => []
| [a] => [a]
| (x :: (y :: ys)) => 
  have : List.length (first_half (x :: (y :: ys))) < List.length (x :: (y :: ys)) := length_first_half
  have : List.length (second_half (x :: (y :: ys))) < List.length (x :: (y :: ys)) := length_second_half
  merge (mergesort <| first_half (x :: (y :: ys))) (mergesort <| second_half (x :: (y :: ys)))
termination_by mergesort xs => xs.length

def l := [1, 2, 3]
#eval (l).length
#eval l.length
#eval l.take 1

#eval mergesort [1, 3, 2]
#eval mergesort [3, 2, 1]
#eval mergesort [5, 4, 3, 1, 2]
