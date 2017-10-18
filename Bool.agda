{-
Each file is a module with the same name as the file. We thus declare
-}

module Bool where

{-
To type-check an Agda-file, you issue the command "load" (^C^L).
For example, you can type-check the file Bool.agda with only the single line above.

We can define data types in a similar way as in Haskell, but the syntax is different since we have more general types in Agda. In Haskell we can declare

data Bool = True | False

but in Agda we have more verbose syntax:
-}

data Bool : Set where
  true  : Bool
  false : Bool

{-
Note that Agda has a standard library where many common types and functions are defined.

Functions in Agda are defined much like in Haskell, but whereas Haskell infers the type of a function, we must declare this type in Agda:
-}

not : Bool -> Bool
not true = false
not false = true

{-
In Agda we have unicode and can for example write → (by typing \to) instead of -> and ¬ (by typing \neg) instead of not:
-}

¬ = not

{-

? becomes { }n  (a "hole" with number n) when type-checked. Holes can be (partly) filled in several ways:

- by writing a complete expression in the hole and issueing the command "give" (^C^SPC);
- by writing a partial expression in the whole and issuing the command "refine" (^C^R);
- by writing the top level function symbol and issuing the command "refine" (^C^R).

For example, you can write the function
-}

¬¬ : Bool → Bool
¬¬ b = ¬ (¬ b)

{-
by gradual refinement. (Note that ¬¬ is a single identifier. Consult the Agda wiki for more information.) First write

¬¬ b = ?

and load the file (^C^L). You will get

¬¬ b = { }0

You can then choose either of the three options above, if you want to fill the hole completely or partially. For example, you can choose the third option and tell Agda that the top-level function symbol is ¬:

¬¬ b = {¬ }0

by doing "refine" (^C^R) while keeping the cursor inside the hole. You will get

¬¬ b = ¬ (¬ { }1)

Again, you can choose either of the three options to instantiate the new hole. Say that this time we choose the second option and write

¬¬ b = ¬ ({¬ ?}1)

After doing refine you will get

¬¬ b = ¬ (¬ { }2)

Finally you completely fill the hole:

¬¬ b = ¬ (¬ {b }2)

and do "give" (^C^SPC), to finish the definition.

Another way to define functions is by case analysis (pattern matching). Agda will create the patterns for you in the following way. Consider the example of defining "and" for booleans. The complete definition is
-}
-- by writing the pattern variable in a hole and do ^C^C

-- Exercise: write not by gradual refinement and case analysis

-- This is how you declare an infix operator:

_&&_ : Bool → Bool → Bool
b && true  = b
b && false = false

infixl 50 _&&_

{-
First note how you declare an infix operator with underscores. in order to define this function by gradual refinement, we begin by writing

b && c = ?

After type-checking this becomes

b && c = { }0

Now write c in the hole and write ^C^C in order to do pattern matching on c. You will get

_&&_ : Bool → Bool → Bool
b && true  = { }1
b && false = { }2

and then you can instantiate the holes in the same way as above.

Agda makes it possible to declare mixfix operators in general. For example:
-}

if_then_else_ : Bool → Bool → Bool → Bool
if true  then y else z = y
if false then y else z = z

{-
Exercise: Define logical or and logical equivalence

_||_ : Bool → Bool → Bool
_<=>_ : Bool → Bool → Bool

by pattern matching and refinement, using ^C^C, ^C^R, and ^C^SPC.

Compute some instances using ^C^N!
-}
