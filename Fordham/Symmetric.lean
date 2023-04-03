import Mathlib.Data.Nat.Bitwise
import Fordham.Util

/-!
# Symmetric cryptography

A central idea behind cryptography is that two parties want to communicate, and prevent a malicious
third party from spying in on their communication.

It is relatively clear to see (and it can be formalized and mathematically proven) that if there are
no secrets, then there is no hope 

The premise of symmetric cryptography is that the two communicating parties `A` (Alice) and `B` (Bob)
share some secret information, a **secret key**, that they use to encrypt and decrypt 
-/

namespace Hidden

/-
In this section we will introduce the **One Time Pad** encryption method, which is based off the 
boolean `xor` function.
-/
def xor : Bool → Bool → Bool
  | true, true   => false
  | true, false  => true
  | false, true  => true
  | false, false => false

infix:1000 "^^" => xor

theorem xor_comm (a b : Bool) : a ^^ b = b ^^ a := by
  cases a <;> cases b <;> rfl

theorem xor_assoc (a b c : Bool) : a ^^ (b ^^ c) = (a ^^ b) ^^ c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor_self (a : Bool) : a ^^ a = false := by
  cases a <;> rfl  

theorem xor_false_eq_self (a : Bool) : false ^^ a = a := by
  cases a <;> rfl

theorem xor_xor_eq_self (a b : Bool) : a ^^ (a ^^ b) = b := by
  rw [xor_assoc, xor_self, xor_false_eq_self]

def lxor (l₁ l₂ : List Bool) : List Bool :=
  let pairs := List.zip l₁ l₂
  List.map (fun (a, b) => a ^^ b) pairs

/-
Lets use `Nat`s instead, because they are faster and easier to work with
-/
scoped instance(priority := 100000000) : Repr Nat where
  reprPrec n _ := binaryRepr n


-- The key functions of OTP:

def encrypt (key plaintext : Nat) := key ^^^ plaintext

def decrypt (key ciphertext : Nat) := key ^^^ ciphertext


-- Here's an example!
def my_plaintext := encodeAsNat "Hello!"
def my_key := 0b1001111011000011111001011011100110100011100101

-- Calculate the ciphertext:
def ciphertext := encrypt my_key my_plaintext

-- Decrypt the ciphertext:
def decryptedtext := decrypt my_key ciphertext

#eval decryptedtext

#eval decodeFromNat decryptedtext

/-
One major downside of OTP is that the keys have to be the same size as the plaintext messages!
-/

-- It is very good at securing 
def matejs_secret := 0b1100011111011100100111000110111

end Hidden
