import Mathlib.Data.List.Perm

/-! ### Merge sort -/


section merge_sort

-- TODO(Jeremy): observation: if instead we write (a :: (split l).1, b :: (split l).2), the
-- equation compiler can't prove the third equation

/-- Split `l` into two Lists of approximately equal length.
     split [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) -/
@[simp] def split : List α → List α × List α
| []       => ([], [])
| (a :: l) => let (l₁, l₂) := split l
              (a :: l₂, l₁)

theorem split_cons_of_eq (a : α) {l l₁ l₂ : List α} (h : split l = (l₁, l₂)) :
  split (a :: l) = (a :: l₂, l₁) := by
    rw [split, h]

theorem length_split_le : ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → length l₁ ≤ length l ∧ length l₂ ≤ length l
| [] ,_  ,_  rfl => ⟨nat.le_rfl 0, nat.le_rfl 0⟩
| (a::l) l₁' l₂' h   => by
  cases e : split l with l₁ l₂,
  injection (split_cons_of_eq _ e).symm.trans h, substs l₁' l₂',
  cases length_split_le e with h₁ h₂,
  exact ⟨nat.succ_le_succ h₂, nat.le_succ_of_le h₁⟩

theorem length_split_lt {a b} {l l₁ l₂ : List α} (h : split (a::b::l) = (l₁, l₂)) :
  length l₁ < length (a::b::l) ∧ length l₂ < length (a::b::l) := by
  cases e : split l with l₁' l₂',
  injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h, substs l₁ l₂,
  cases length_split_le e with h₁ h₂,
  exact ⟨nat.succ_le_succ (nat.succ_le_succ h₁), nat.succ_le_succ (nat.succ_le_succ h₂)⟩

theorem perm_split : ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → l ~ l₁ ++ l₂
| []     ._  ._  rfl => perm.rfl _
| (a::l) l₁' l₂' h   => by
  cases e : split l with l₁ l₂,
  injection (split_cons_of_eq _ e).symm.trans h, substs l₁' l₂',
  exact ((perm_split e).trans perm_append_comm).cons a,

/-- Merge two sorted Lists into one in linear time.
     merge [1, 2, 4, 5] [0, 1, 3, 4] = [0, 1, 1, 2, 3, 4, 4, 5] -/
def merge : List α → List α → List α
| []       l'        => l'
| l        []        => l
| (a :: l) (b :: l') => if a ≼ b then a :: merge l (b :: l') else b :: merge (a :: l) l'

include r
/-- Implementation of a merge sort algorithm to sort a List. -/
def merge_sort : List α → List α
| []        => []
| [a]       => [a]
| (a::b::l) => by
  cases e : split (a::b::l) with l₁ l₂,
  cases length_split_lt e with h₁ h₂,
  exact merge r (merge_sort l₁) (merge_sort l₂)

using_well_founded
{ rel_tac => λ_ _, `[exact ⟨_, inv_image.wf length nat.lt_wf⟩],
  dec_tac => tactic.assumption }

theorem merge_sort_cons_cons {a b} {l l₁ l₂ : List α}
  (h : split (a::b::l) = (l₁, l₂)) :
  merge_sort r (a::b::l) = merge r (merge_sort r l₁) (merge_sort r l₂) := by
  suffices : ∀ (L : List α) h1, @@and.rec
    (λ a a (_ : length l₁ < length l + 1 + 1 ∧
      length l₂ < length l + 1 + 1), L) h1 h1 = L,
  { simp [merge_sort, h], apply this },
  intros, cases h1, rfl

end merge_sort
