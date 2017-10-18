module Nat where

open import Bool

{-
We begin by defining the data type of unary natural numbers
-}

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

one = succ zero
two = succ one

{-
You can get access to decimal notation and machine arithmetic  by using "builtin" numbers, see below.

Without machine arithmetic we define + and * by primitive recursion:
-}

_+_ : Nat → Nat → Nat
m + zero   = m
m + succ n = succ (m + n)

_*_ : Nat → Nat → Nat
m * zero   = zero
m * succ n = m + (m * n)

{-
We can declare precedences and associations in Agda. Here we can declare that both + and * are infix operations which associate to the left and that * binds harder than +:
-}

infixl 60 _+_
infixl 70 _*_

{-
Thus x + y + z parses as (x + y) + z:
-}

f : Nat → Nat → Nat → Nat
f x y z = x + y + z

{-
The following "pragma" declares that Nat corresponds to the computer's built-in natural numbers.
-}

{-# BUILTIN NATURAL Nat #-}

zerodecimal : Nat
zerodecimal = 0

{- 
It also lets you write elements of Nat by using decimal notation. Moreover, if you write
-}

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

{-
you can use binary machine arithmetic for computing + and *.

There are many other built in types: integers, floats, strings, and characters. See the Agda wiki for more information.

Exercise: 
(a) Define the factorial function

factorial : Nat → Nat

Compute the result of factorial for some instances by normalizing with ^C^N. How large factorials can Agda compute?

(b) Define the power function

power : Nat → Nat → Nat
--}

-- The equality test

_==_ : Nat → Nat → Bool
zero == zero = true
zero == succ n = false
succ m == zero = false
succ m == succ n = m == n

