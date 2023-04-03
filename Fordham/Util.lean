import YatimaStdLib.ByteArray
import YatimaStdLib.Nat

def encodeAsBytes : String → ByteArray := String.toUTF8

def decodeFromBytes : ByteArray → String := 
  fun s => s |>.data
             |>.map (fun u => Char.ofNat u.toNat) 
             |>.toList 
             |> String.mk

def encodeAsNat : String → Nat := ByteArray.asLEtoNat ∘ encodeAsBytes

def decodeFromNat : Nat → String := decodeFromBytes ∘ Nat.toByteArrayLE

def binaryRepr (n : Nat) : String :=
  let bits := n.toBits
  "0b" ++ String.mk (bits.map fun b => if b == .one then '1' else '0')
