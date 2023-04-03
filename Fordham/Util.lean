import YatimaStdLib.ByteArray

def encodeAsBytes : String → ByteArray := String.toUTF8

def decodeFromBytes : ByteArray → String := 
  fun s => s |>.data
             |>.map (fun u => Char.ofNat u.toNat) 
             |>.toList 
             |> String.mk

def encodeAsNat : String → Nat := ByteArray.asLEtoNat ∘ encodeAsBytes

def decodeFromNat : Nat → String := decodeFromBytes ∘ Nat.toByteArrayLE
