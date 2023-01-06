import Mathlib

structure Token where
  word : String
  idx : Nat
  reversed : Bool

def lt (a : Token) (b : Token) : Bool := if a.word < b.word then sorry else sorry

def reverse (s : String) : String := String.join <| s.toList.reverse.map Char.toString

def getToken
    (n : Nat)
    (pair : String × String)
: Token × Token :=
  ⟨{word := pair.fst, idx := n, reversed := False}, {word := pair.snd, idx := n, reversed := True}⟩

#eval reverse "abc"

def palindromicPairs (words : List String) : List (List Nat) :=
  let words_and_reversals : List (String × String) := words.map (λ w => ⟨w, reverse w⟩)
  let ⟨forwards, reverses⟩ := List.unzip <| List.mapIdx getToken words_and_reversals
  let tokens := forwards ++ reverses
  sorry

#check List.mapIdx getToken
