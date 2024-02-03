{-# LANGUAGE QuasiQuotes #-}
module Examples where

import Lib.RawString

{- Here, you can write your examples to test your program!
 - Some remarks:
 -      - This DOES NOT support multiple arguments in lambda terms i.e., \x y -> x y is NOT allowed... You would need to write \x -> \y -> x y..
 -
 -      - In this language, lists are "defined" as follows:
 -          data [a]
 -              = Cons (a, [a])
 -              | Nil
 -         Note how ``Cons`` takes in a tuple.
 -
 -      - In this language, naturals are "defined" as follows:
 -          data Nat 
 -              = Succ Nat
 -              | Zero
 -
 - Again, some examples are included to give you a feel for the grammar, but feel free to write up your own test cases as well! 
 -
 - To use the parser, type
 -      unsafeParseTerm <some string here>
 - and it will either throw an error (could not parse) OR
 - return the AST of the lambda term.
 -}


{- Write your own examples here! -}
myExample :: String
myExample = [r|
|]


{- Given examples! -}

-- Solution: [a] -> [a]
givenExample0 :: String 
givenExample0 = [r| 
    fix (\f -> \lst -> case lst of
            Nil -> Nil ; -- << This semi colon is VERY important
            Cons a -> case a of
                (r, rs) -> Cons (r, f rs)
    )
|]

-- Solution: Occurs check
givenExample1 :: String 
givenExample1 = [r| 
    \x -> x x
|]

-- Solution: () -> ()
givenExample2 :: String 
givenExample2 = [r| 
    \n -> case n of
        () -> () 
|]

-- Solution: Match failure
givenExample3 :: String 
givenExample3 = [r| 
    \n -> case n of
        Zero -> ()  ; -- << This semicolon is very important!
        Succ n -> n 
|]

-- Solution: a -> (a -> b) -> (b, a -> b)
givenExample4 :: String 
givenExample4  = [r| 
    \x -> \y -> (y x, y)
|]

-- Solution: [Nat -> Nat]
givenExample5 :: String 
givenExample5  = [r| 
    Cons (Succ, Cons (\x -> Zero, Nil))
|]

-- Solution: Nat
givenExample6 :: String 
givenExample6  = [r| 
    Succ (Succ Zero)
|]

-- Solution: ()
givenExample7 :: String 
givenExample7  = [r| 
    ()
|]
