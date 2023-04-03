import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option linter.deprecated false 

/-!
# A slightly more complicated example of formally verified software:

Because Lean is function, loops don't work exactly the way you would hope they do. The replacement
for iterating over loops is the use of **recursion** where we call a function in its own definition.

For example:
-/
def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-
Exponentiation is also defined recursively:
-/

#check Nat.pow

/-
To evaluate `a ^ N` we would need to unfold the definition `N` times, and calculate `N` multiplications.
`O(N)`

If `N` is small this is no issue, but we will see examples where we want `N` to be very large.
That is why we will now define a faster multiplication, based on the **square and multiply** method.
-/
def fastPowAux (n : Nat) (bs : List Bool) : Nat :=
  match bs with
  | [] => 1
  | true :: bs' => n * (fastPowAux n bs')^2
  | false :: bs' => (fastPowAux n bs')^2

-- This takes `O(log N)`
def fastPow (n m : Nat) : Nat :=
  let bs := Nat.bits m
  fastPowAux n bs

/-
Having a faster definition is nice, but we want to be sure that we haven't messed anything up for 
the sake of speed.

The following is a fully self-contained proof that the two definitions are equivalent.
-/
theorem Nat.pow_eq_fastPow (n : Nat) : ∀ m, n ^ m = fastPow n m := by
  apply Nat.binaryRec -- This is the **key** lemma that is needed to get the proof rolling
  · simp only [pow_zero, fastPow, fastPowAux]
  · intros b m h
    cases b
    · simp only [Nat.bit, cond_false]
      induction m
      · simp [pow_zero, fastPow, fastPowAux]
      · rename_i m _
        have : Nat.succ m ≠ 0 := by simp only [ne_eq, succ_ne_zero, not_false_iff]
        simp only [fastPow, fastPowAux, ne_eq, succ_ne_zero, not_false_iff, bit0_bits]
        have h2 : n ^ (m.succ + m.succ) = (n ^ m.succ)^2 := by ring
        rw [bit0, h2]
        simp only [fastPow] at h
        simp only [h]
    · simp only [Nat.bit, cond_true]
      have : n ^ (bit0 m + 1) = n * n ^ (bit0 m) := by ring
      simp only [fastPow, fastPowAux, bit1_bits]
      simp only [bit1]
      rw [this]
      induction n
      · simp only [zero_eq, ne_eq, bit0_eq_zero, zero_mul]
      · simp only [bit0._eq_1, mul_eq_mul_left_iff, succ_ne_zero, or_false, this, bit0]
        rename_i n _
        have h2: (n.succ) ^ (m + m) = (n.succ ^ m)^2 := by ring
        rw [h2]
        dsimp only [fastPow] at h
        simp only [h]

/-
Here is a slightly faster way of calculating exponentials, but the proof that it is equivalent to
the above two is left as an exercise (translation: I couldn't figure it out)
-/
def powMod (base exp mod : Nat) : Nat :=
  let rec aux (base exp acc : Nat) :=
    match h : exp with
    | 0 => acc
    | Nat.succ k =>
      let exp' := exp / 2
      have : exp' < exp := Nat.bitwise_rec_lemma (by linarith)
      if exp % 2 == 0 then
        aux (base * base % mod) exp' acc
      else
        aux (base * base % mod) exp' (acc * base % mod)
  aux base exp 1
termination_by _ => exp -- Lean needs to know any recursive function terminates
