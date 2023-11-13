import Fordham.Util

/-!
# Just how difficult is the Discrete Logarithm Problem?

The naive way to break the discrete log problem (trial multiplication) is slow, and inefficient even
for small exponents. But there are much more clever algorithms to break it.

A cryptosystem's level of security can be measured by its number of "**bits** of security".
Roughly this is a measure of the log of the number of computations that a computer has to do to
break the cryptosystem.

For example, my laptop can turbo up to 4.2 GHz, which means I can do roughly `2 ^ 32` operations a
second.
-/

/-
The fastest (publicly) known algorithm for computing the discrete logarithm (also factorization) is
called the **General Numberfield Sieve Method**.

It has a runtime of: `≈ 2 * (ln n)^(1/3) * (ln ln n)^(2/3)`
-/

def E := 2.7182818

def ln : Float → Float := Float.logBase E

def exponent (n : Nat) : Float :=
  2 * (n.toFloat * ln 2)^(1/3 : Float) * (ln (n.toFloat * ln 2)) ^ (2/3 : Float)

def complexity (n : Nat) : Float := E ^ (exponent n)

def bits_of_security (n : Nat) : Float := (exponent n) * Float.log2 E

/-
Another way of thinking about it is in terms of the economic cost to break a cryptosystem's security.

Amazon rents out some really powerful servers for a cost. The following chart, taken from the
fantastic free book [The Joy of Cryptography](https://joyofcryptography.com/), quantifies this
in the following terms:

Clock cycle  |  approx. cost  |    reference
-----------------------------------------------
   2 ^ 50         $3.50            cup of coffee
   2 ^ 55         $100             decent tickets to a Portland Trailblazers game
   2 ^ 65         $130,000         Median home price in Oshkosh, WI
   2 ^ 75         $130 million     Budget of one of the Harry Potter movies
   2 ^ 85         $140 billion     GDP of Hungary
   2 ^ 92         $20 trillian     GDP Of the United States
   2 ^ 99         $2 quadrillion   all of human economic activity since 300,000 BC
   2 ^ 128        really a lot     a billion human civilizations' worth of effort
-/
