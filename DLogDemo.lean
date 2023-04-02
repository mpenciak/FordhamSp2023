import YatimaStdLib.Zmod
import YatimaStdLib.ByteArray

def p : Nat := 0xffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca237327ffffffffffffffff

abbrev F := Zmod p 

def a : Nat := 2

def d : Nat := 65535

def b : Nat := Nat.powMod p a d

def g : F := 2

def message : String := "Hello Math 2001!"

def encodeMessage : String → Nat :=
  fun s => s.toUTF8.asLEtoNat

def decodeMessage : Nat → String :=
  fun s => s |>.toByteArrayLE
             |>.data
             |>.map (fun u => Char.ofNat u.toNat)
             |>.toList
             |> String.mk

def plaintext : Nat := encodeMessage message

#eval plaintext

def k : Nat := 89123949

def r := Nat.powMod p a k

def t := (Nat.powMod p b k) * plaintext % p

#eval r
#eval t

def invR := Int.modInv r p

#eval invR * r % p

def plaintext' := t * (Nat.powMod p invR.toNat d) % p
