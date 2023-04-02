import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.deprecated false 

def fastPowAux (n : Nat) (bs : List Bool) : Nat :=
  match bs with
  | [] => 1
  | true :: bs' => n * (fastPowAux n bs')^2
  | false :: bs' => (fastPowAux n bs')^2

def fastPow (n m : Nat) : Nat :=
  let bs := Nat.bits m
  fastPowAux n bs

theorem Nat.pow_eq_fastPow (n : Nat) : ∀ m, n ^ m = fastPow n m := by
  apply Nat.binaryRec
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
termination_by _ => exp

def length_reverse {α : Type _} (l : List α) : l.reverse.length = l.length := by
  induction l with
  | nil => rfl
  | cons a l' ih => 
    rw [List.reverse_cons, List.length_append, List.length_cons, List.length_cons, List.length_nil, ih]
    