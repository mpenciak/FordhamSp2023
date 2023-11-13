import Fordham.Util
import FFC.MSM

/-!
# Lean 4 as a programming language

In addition to being a theorem prover, Lean 4 is a _functional_ programming language.

It's very young, but there are already starting to be some great resources for using Lean 4 as
a programming language:

https://leanprover.github.io/functional_programming_in_lean/
-/

-- Here's an example of what some Lean 4 code can look like:
#check toByteArrayCore
#check pippengerMSM

open List (reverse length)

/- In addition to the types you are likely familar with, it has all the types you need to program! -/
-- You can have `Float`s:
#check 3.195

-- `Bool`s:
#check true
#check false

-- Lists
def ex1 := [39, 1, 20, 39, 5, 77]
def ex2 := ["hi", "everyone"]

#check ex1
#check ex2

-- And all the functions you'd expect to manipulate these objects
#eval length ex1
#eval reverse ex1

/-
What sets Lean 4 apart from almost any other programming language out there, is that you can also
**reason** about the functions you define.

In this example we will prove that `length ∘ reverse = length` on Lists.

To prove this theorem, we will use a few known lemmas (these have been previously proven):

`length_nil : length [] = 0`
`length_cons : length (a :: as) = Nat.succ (length as)`
a :: as = [a, ...]
`length_append : length (as ++ bs) = length as + length bs`
`reverse_cons : reverse (a :: as) = (reverse as) ++ [a]`
-/

#check List.reverse_cons

#check Nat

open List in
theorem length_reverse {α : Type _} (l : List α) : length (reverse l) = length l := by
  induction l
  · rfl
  · rename_i head tail ih
    rw [reverse_cons, length_append, length_cons, length_cons, length_nil, ih]
