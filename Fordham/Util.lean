-- import YatimaStdLib.ByteArray
-- import YatimaStdLib.Nat
import FFC.Util.Bit

def encodeAsBytes : String → ByteArray := String.toUTF8

def decodeFromBytes : ByteArray → String :=
  fun s => s |>.data
             |>.map (fun u => Char.ofNat u.toNat)
             |>.toList
             |> String.mk

def ByteArray.asLEtoNat (b : ByteArray) : Nat :=
  b.data.data.enum.foldl (init := 0)
    fun acc (i, bᵢ) => acc + bᵢ.toNat.shiftLeft (i * 8)

def encodeAsNat : String → Nat := ByteArray.asLEtoNat ∘ encodeAsBytes

def toByteArrayCore : Nat → Nat → ByteArray → ByteArray
  | 0, _, bytes => bytes
  | fuel + 1, n, bytes =>
    let b: UInt8 := UInt8.ofNat (n % 256)
    let n' := n / 256
    if n' = 0 then (bytes.push b)
    else toByteArrayCore fuel n' (bytes.push b)

/-- Convert Nat to Little-Endian ByteArray -/
def Nat.toByteArrayLE (n : Nat) : ByteArray :=
  toByteArrayCore (n + 1) n default

def decodeFromNat : Nat → String := decodeFromBytes ∘ Nat.toByteArrayLE

def binaryRepr (n : Nat) : String :=
  let bits := n.toBits
  "0b" ++ String.mk (bits.map fun b => if b == .one then '1' else '0')

def Float.logBase (base arg: Float) : Float := Float.log arg / Float.log base
