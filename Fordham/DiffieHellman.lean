import YatimaStdLib.Nat

/-!
# Asymmetric cryptography

How can Alice and Bob derive a shared secret, if a malicious third party (Carol) is listening
in on every single message they send back and forth?

The key idea is that of a **trapdoor function**. A function `f : α → β` which is efficient to compute
on a given input `a : α`, but difficult to invert without any extra information. 

There are a number of trapdoor functions, in this section we will focus on the **discrete logarithm**
problem.
-/

def p := 0xFFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3D2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F3655D23DCA3AD961C62F356208552BB9ED529077096966D70C354E4ABC9804F1746C08CA18217C32905E462E36CE3B39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9E2BCBF6955817183995497CEA956AE515D2261898FA05105728E5A8AACAA68FFFFFFFFFFFFFFFF

def g := 2

-- Function that takes a secret key to a public key
def pk_of_sk := fun sk => Nat.powMod p g sk

-- Example:
def a := 192409812319230912385230490123

def A := pk_of_sk a

#eval A

def b := 69459649569234072347820345023094587345

def B := pk_of_sk b

#eval B

def shared_secret₁ := Nat.powMod p B a

def shared_secret₂ := Nat.powMod p A b

#eval shared_secret₁
#eval shared_secret₂
#eval shared_secret₁ == shared_secret₂