import YatimaStdLib.Zmod
import Fordham.Util

/-!
# ElGamal Encryption and Decryption

ElGamal is another encryption method that relies on the hardness of the Discrete Logarithm
(but doesn't go through an intermediate of symmetric cryptography to encrypt messages)
-/

structure PublicKey where
  prime : Nat       -- p
  generator : Nat   -- a
  publicPower : Nat -- b

structure SecretKey where
  decryptKey : Nat  -- d

structure CipherText where
  hiddenKey : Nat     -- r
  hiddenMessage : Nat -- t

def encrypt (pk : PublicKey) (randomness : Nat) (message : Nat) : CipherText := 
  let ⟨p, a, b⟩ := pk
  let k := randomness
{
  hiddenKey := Nat.powMod p a k
  hiddenMessage := (Nat.powMod p b k) * (message) % p
}

def decrypt (ct : CipherText) (sk : SecretKey) (pk : PublicKey) : Nat :=
  let ⟨p, _, _⟩ := pk
  let ⟨d⟩ := sk
  let ⟨r, t⟩ := ct
  let inv_r := Int.modInv r p |>.toNat
  t * (Nat.powMod p inv_r d) % p

/- # Example -/

def p : Nat := 0xffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca237327ffffffffffffffff

def a : Nat := 2

def d : Nat := 65535 -- SECRET!

def b : Nat := Nat.powMod p a d

def examplePk : PublicKey := {
  prime := p
  generator := a
  publicPower := b
}

def exampleSk : SecretKey := {
  decryptKey := d
}

def message : String := "Hello Math 2001!"

def plaintext : Nat := encodeAsNat message

def k : Nat := 89123949

def exampleCipherText : CipherText := encrypt examplePk k plaintext

def exampleDecryptedText : Nat := decrypt exampleCipherText exampleSk examplePk
