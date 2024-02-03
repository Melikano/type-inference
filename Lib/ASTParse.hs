module Lib.ASTParse where
import Text.ParserCombinators.ReadP (ReadP, (<++))
import qualified Text.ParserCombinators.ReadP as ReadP

import Data.Char
import Data.Functor
import Data.Maybe
import Data.Tuple

import qualified Lib.AST as AST
import Lib.AST (LambdaTerm)

{- This includes a collection of functions used to parse a lambda term..
 -
 - How to use:
 -      ``unsafeParseTerm <some lambda term here>``
 - and this should return a LambdaTerm. If the parse fails,
 - then this will throw an error.
 -
 - Known bugs:
 -      - Error messages are terrible -- the author (Jared) hasn't had time
 -       to write his own parser library, so he's still using the
 -       ReadP parser library which doesn't support error messages!
 -
 - Please report any other bugs to the author (Jared) and 
 - you guys can hopefully get them resolved! 
 -
 - See ``Examples.hs`` for examples of programs that it parses...
 -}

----------------------------
-- Functions to parse lambda term..
----------------------------
unsafeParseTerm :: String -> LambdaTerm
unsafeParseTerm inp = case parseTerm inp of
    Just res -> res
    Nothing -> error "Parse error."

parseTerm :: String -> Maybe LambdaTerm
parseTerm inp = case ReadP.readP_to_S (junk *> terms0 <* ReadP.eof) inp of
    [(ast, [])] -> Just ast
    -- rs -> error $ show rs
    _ -> Nothing

----------------------------
-- Some basic parser definitions for
-- this parser built on top of 
-- Text.ParserCombinators.ReadP
----------------------------
junk :: ReadP ()
junk = 
    ReadP.skipSpaces
    *> void (ReadP.many (ReadP.string "--" 
            *> (ReadP.munch (/='\n'))
            *> ReadP.skipSpaces))

token :: ReadP a -> ReadP a
token pa  = pa <* junk

symbol :: String -> ReadP String
symbol = token . ReadP.string

keywords :: [String] 
keywords = 
    [ "fix"
    , "Succ"
    , "Zero"

    , "Cons"
    , "Nil"

    , "case"
    -- , "lcase"
    -- , "ncase"
    -- , "pcase"
    -- , "ucase"
    , "of"
    ]

ident :: ReadP String
ident = token $ do
    inp <- ReadP.look
    case inp of
        c:_ 
            | isAlpha c -> do 
                cs <- ReadP.munch1 isAlphaNum
                if cs `notElem` keywords
                    then return cs
                    else ReadP.pfail
            | otherwise -> ReadP.pfail
        [] -> ReadP.pfail

terms0 :: ReadP LambdaTerm
-- terms0 = ReadP.chainl1 term1 (pure AST.App)
terms0 = term1 >>= f
  where
    f acc = (do t <- term1' ; f (AST.App acc t)) <++ pure acc

term1 :: ReadP LambdaTerm
term1 = ReadP.choice
    [ builtInPrimitiveTerm <++ varTerm
    , absTerm
    , caseTerm
    , fixTerm
    , tupleOrBracketedTerm0sTerm    
    ]

term1' :: ReadP LambdaTerm
term1' = ReadP.choice
    [ builtInPrimitiveTerm <++ varTerm
    , tupleOrBracketedTerm0sTerm    
    ]

varTerm :: ReadP LambdaTerm
varTerm = AST.Var <$> ident

fixTerm :: ReadP LambdaTerm
fixTerm = symbol "fix" *> (AST.FFix <$> term1)

tupleOrBracketedTerm0sTerm :: ReadP LambdaTerm
tupleOrBracketedTerm0sTerm = ReadP.between (symbol "(") (symbol ")") 
    $ ReadP.option AST.Unit $ do
        t1 <- terms0
        t2 <- ReadP.option Nothing (fmap Just $ symbol "," *> terms0)
        return $ case t2 of
            Just t2' -> AST.Pair t1 t2'
            Nothing -> t1

builtInPrimitiveTerm :: ReadP LambdaTerm
builtInPrimitiveTerm = (AST.Cons <$ token (symbol "Cons"))
    <++ (AST.Nil <$ symbol "Nil")
    <++ (AST.Succ <$ symbol "Succ")
    <++ (AST.Zero <$ symbol "Zero")

absTerm :: ReadP LambdaTerm
absTerm = AST.Abs <$> (symbol "\\" *> ident <* (symbol "." <++ symbol "->")) <*> terms0

caseTerm :: ReadP LambdaTerm
caseTerm = (symbol "case" *> terms0 <* symbol "of") >>= f
  where
    f caseon = tuplecase <++ primitivecase
      where
        tuplecase = do
            args <- ReadP.between (symbol "(") (symbol ")") $ ReadP.option 
                        Nothing 
                        (fmap Just $ (,) <$> (ident <* symbol ",") <*> ident) 
            symbol "->"
            t' <- terms0
            return $ case args of
                Just args -> AST.PCase caseon (args, t')
                Nothing -> AST.UCase caseon t'
    
        primitivecase = ncase <++ lcase

        ncase = fmap (uncurry (AST.NCase caseon)) 
            $ ((,) <$> (ncasez <* symbol ";") <*> ncases) 
                <++ (fmap swap $ (,) <$> (ncases <* symbol ";") <*> ncasez)
            {-
            (t0,arg) <-  
            return $ AST.NCase caseon t0 arg
            -}
          where
            ncasez = symbol "Zero" *> symbol "->" *> terms0
            ncases = (,) <$> (symbol "Succ" *> ident <* symbol "->") <*> terms0

        -- duplicated code
        lcase = fmap (uncurry (AST.LCase caseon)) 
            $ ((,) <$> (lcasen <* symbol ";") <*> lcasec) 
                <++ (fmap swap $ (,) <$> (lcasec <* symbol ";") <*> lcasen)
          where
            lcasen = symbol "Nil" *> symbol "->" *> terms0
            lcasec = (,) <$> (symbol "Cons" *> ident <* symbol "->") <*> terms0
            
