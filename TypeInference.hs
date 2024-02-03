module TypeInference where

import           Lib.AST
import           Lib.Monads

-- | autoGraderTypeInference 
-- You should implement this function! This function should take a LambdaTerm
-- and output either:
--      - Left: an informative error message (either a free variable error,
--          or a type inferencing error such as match failure or occurs check)
--      - Right: the most general inferred type of the lambda term
-- Wahoo!! Last assignment you're nearly there :D


throwError' :: String -> StateT s (Either String) a
throwError' error = lift (Left error)

type Judger a = StateT (Int, Context) (Either String) a
type Context = [(String, String)]

type Sub = (String, LambdaTyTerm)

-- data type for type equations:
-- they can either be type existence with list of bound type vars and list of type equations or type equality between two type terms
data TypeEqns v = TypeExist [v] [TypeEqns v] | TypeEqn (TyTerm () v, TyTerm () v)
    deriving(Show)

type SolvedEqn v = ([v], [v], [Sub])
-- fold function for typeEqn type
-- for TypeEqn constructor -> just apply g type equality
-- for TypeExist constructor -> apply f on list of bound variables and map fold on inner list of type eqns
foldTypeEqns
    :: ([v] -> [b] -> b) -> ((TyTerm () v, TyTerm () v) -> b) -> TypeEqns v -> b
foldTypeEqns f g (TypeEqn eq     ) = g eq
foldTypeEqns f g (TypeExist l eqs) = f l (map (foldTypeEqns f g) eqs)

-- linearize function restricted to input list of vars
-- takes each bound variable, finds the substitution for it (if exist)
-- applies the substitution and does the matching if needed (coalesce function)
-- recursively calls for the rest of bound variables
-- if there is no substitutions for a bound variable then it returns it as the list of not-substituted vars
-- so they can be passed up in the main algorithm
restrictedLinearize
    :: [String] -> [String] -> [Sub] -> Either String ([String], [Sub])
restrictedLinearize []       rbs subs = return (rbs, subs)
restrictedLinearize (b : bs) rbs subs = do
    case lookup b subs of
        Nothing -> restrictedLinearize bs (b : rbs) subs
        Just s  -> do
            cSubs <- coalesce (b, s) subs
            restrictedLinearize bs rbs cSubs

-- function that gathers all free variables, bound variables and substitutions of a list of equations into a 
-- triple of form ([frees], [bounds], [subs]) of type SolvedEqns
getAllEqns
    :: [Either String (SolvedEqn String)] -> Either String (SolvedEqn String)
getAllEqns = foldr allEqns (Right ([], [], []))  where
    allEqns newEitherFBS accEitherFBS = do
        (f , b , s ) <- newEitherFBS
        (fs, bs, ss) <- accEitherFBS
        -- frees = union of all frees
        -- bounds = disjoint union of bounds (as they must be distinct)
        -- subs = first subs appended onto the second
        return (fs ++ f, disjointUnion b bs, ss ++ s)

-- helper function to implement disjoint union
-- if an element exists in both lists, remove it
-- otherwise, add it to the result
disjointUnion :: Eq a => [a] -> [a] -> [a]
disjointUnion [] ys = ys
disjointUnion (x : xs) ys | x `elem` ys = disjointUnion xs (filter (/= x) ys)
                          | otherwise   = x : disjointUnion xs ys

-- function for solving type equations
-- fold on TypeEqns is used to implement the algorithm
-- ON TypeEqn  -> 
-- unify two terms with each other to obtain list of subs, 
-- append all vars of the two terms together to obtain the free vars,
-- empty list as bound vars because there are no bound vars
-- ON TypeExist -> 
-- gather all inner equations into the form of a solved equation ([v], [v], [sub])
-- call restricted linearize for bound vars to sub out the bound vars
-- and get remaining bound vars and subs
-- remove bound vars from free vars to get new free vars
-- pass up (new free vars, remaining bounds, remaining subs)
solveEquations :: TypeEqns String -> Either String (SolvedEqn String)
solveEquations = foldTypeEqns procExist procEqn  where
    procExist
        :: [String]
        -> [Either String ([String], [String], [Sub])]
        -> Either String ([String], [String], [Sub])


    procExist bounds eqns = do
        (innerFrees, innerBounds, innerSubs) <- getAllEqns eqns
        -- we should call restricted linearize for ALL bound vars
        -- so we append inner bounds and current bounds
        -- and then restricted linearize
        let allBounds = bounds ++ innerBounds
        (remainingBounds, remainingSubs) <- restrictedLinearize allBounds
                                                                []
                                                                innerSubs
        return
            ( filter (`notElem` allBounds) innerFrees
            , remainingBounds
            , remainingSubs
            )

    procEqn (lt1, lt2) = do
        let esubs = unify (lt1, lt2)
        subs <- esubs
        return (vars lt1 ++ vars lt2, [], subs)

-- function to get all variables of a lambda type term     
vars :: LambdaTyTerm -> [String]
vars (TyVar () a      ) = [a]
vars (TyArr     () l r) = vars l ++ vars r
vars (TyProduct () l r) = vars l ++ vars r
vars (TyList () a     ) = vars a
vars _                  = []

-- function for applying substitutions
-- if first one is a type var then just check if the var that is going to be substituted is equal to that var, return the term
-- which is specified in sub otherwise return the type var itself
-- in other cases if there are inner terms, call the sub func recursively on them otherwise return themselves as there are no terms to apply substitution on    
sub :: LambdaTyTerm -> Sub -> LambdaTyTerm
sub (TyVar () z) (x, l) | x == z    = l
                        | otherwise = TyVar () z
sub (TyArr     () l  r ) s = TyArr () (sub l s) (sub r s)
sub (TyProduct () p1 p2) s = TyProduct () (sub p1 s) (sub p2 s)
sub (TyList () a       ) s = TyList () (sub a s)
sub (TyNat  ()         ) s = TyNat ()
sub (TyUnit ()         ) s = TyUnit ()


-- function for detecting occurs check in a sub (x, t)
-- if x should be substituted with TypeVar x then it is trivial and we don't need to include it to list of subs
-- if x is exists in t, then it is occurs check because we can do substitution infinitely so it is occurs check failure
-- else add the sub to the list of subs because it is OK
check :: Sub -> Either String [Sub]
check (y, TyVar () x) | x == y = return []
check sub@(x, term) | x `elem` vars term = Left "occurs check failure"
                    | otherwise          = return [sub]

-- function to match to type terms
-- when matching a term with a type variable we need to check for occurs check (check function above)
-- and otherwise just calling the match function on the inner terms
-- if the structure of two terms is different then it is a matching error (match _ _)
match :: (LambdaTyTerm, LambdaTyTerm) -> Either String [Sub]
match (t           , TyVar () x    ) = check (x, t)
match (TyVar () x  , t             ) = check (x, t)
match (TyArr () l r, TyArr () l' r') = do
    s <- mapM match (zip [l, r] [l', r'])
    return (concat s)
match (TyProduct () p1 p2, TyProduct () p1' p2') = do
    s <- mapM match (zip [p1, p2] [p1', p2'])
    return (concat s)
match (TyList () t, TyList () t') = match (t, t')
match (TyUnit ()  , TyUnit ()   ) = return []
match (TyNat  ()  , TyNat ()    ) = return []
match _                           = Left "matching error"

-- coalesce function takes a substitution (x, t) and a list of substitutions
-- it checks each sub (y, s) in the list of subs
-- if x == y then  then t and s need to be matched to get new subs and then recursively
-- calls coalesce for the rest of subs and prepends new sub to the result
-- otherwise, we should apply substitution in s to get new sub, then check if it has occurs check with y
-- and recursively call coalesce for the rest subs
-- append new and rest subs together and return them as result
coalesce :: Sub -> [Sub] -> Either String [Sub]
coalesce _ [] = Right []
coalesce (x, t) ((y, s) : rest)
    | x == y = do
        matchSubs <- match (t, s)
        recSubs   <- coalesce (x, t) rest
        return (matchSubs ++ recSubs)
    | otherwise = do
        let newS = sub s (x, t)
        newSub  <- check (y, newS)
        recSubs <- coalesce (x, t) rest
        return (newSub ++ recSubs)

-- linearize takes a list of subs, calls coalesce for each sub and rest of the subs
-- to apply subs into other subs if exist
-- the result is a linear list of substitutions (non of them can be applied into another)
linearize :: [Sub] -> Either String [Sub]
linearize []           = return []
linearize (sub : rest) = do
    c <- coalesce sub rest
    l <- linearize c
    return (sub : l)

-- unification of two type terms
-- first match them to get list of possible subs
-- then linearize the subs
unify :: (LambdaTyTerm, LambdaTyTerm) -> Either String [Sub]
unify eq = do
    subs <- match eq
    linearize subs

-- first get the equations by running judgements
-- then solve the equations to get list of free vars, list of bound vars and list of subs
-- linearize free vars and remaining subs to empty all frees
-- the sub for Q (which we passed as the total type) is the answer of type inference 
autoGraderTypeInference :: LambdaTerm -> Either String LambdaTyTerm
autoGraderTypeInference l = do
    result       <- evalStateT (judge l "Q") (0, [])
    (f, b, subs) <- solveEquations result
    finalSubs    <- emptyFrees (filter (/= "Q") f) subs
    case lookup "Q" finalSubs of
        Nothing -> Right (TyVar () "T0")
        Just s  -> Right s

-- call restricted linearize on free vars to get rid of them 
emptyFrees :: [String] -> [Sub] -> Either String [Sub]
emptyFrees []    subs = return subs
emptyFrees frees subs = do
    (f, ss) <- restrictedLinearize frees [] subs
    return ss


mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (x, y) = (x, f y)

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (x, y) = (f x, y)

-- function that sets counter in a state (Ryan's Tutorial notes)
setCounter :: Int -> Judger ()
setCounter counter = do
    modify (mapFst (const counter))

-- function that sets context in a state
setContext :: Context -> Judger ()
setContext context = do
    modify (mapSnd (const context))

-- function that generates a new type var using the counter (Ryan's Tutorial notes)
newTypeVar :: Judger String
newTypeVar = do
    (counter, _) <- get
    setCounter (counter + 1)
    return ("T" ++ show counter)


-- a function for running type judgement
runJudge :: LambdaTerm -> Either String (TypeEqns String)
runJudge l = evalStateT (judge l "Q") (0, [])

-- judge based on the judgments specified in the fixtypes.pdf
-- I really just translated them into haskell :)) I didn't do any important thing
judge :: LambdaTerm -> String -> Judger (TypeEqns String)
-- if var, look up for its type in the context, if not found it means that no it is free
-- otherwise the type var should be equal to the type found in context
judge (Var x) qType = do
    (_, context) <- get
    case lookup x context of
        Nothing -> throwError' "free"
        Just p  -> return (TypeEqn (TyVar () p, TyVar () qType))

judge (Abs x t) qType = do
    (_, context) <- get
    xType        <- newTypeVar
    tType        <- newTypeVar
    setContext $ (x, xType) : context
    tEqns <- judge t tType
    setContext context
    let newEqn = TypeEqn
            (TyVar () qType, TyArr () (TyVar () xType) (TyVar () tType))
    return (TypeExist [xType, tType] (newEqn : [tEqns]))


judge (App left right) qType = do
    lType <- newTypeVar
    rType <- newTypeVar
    lEqns <- judge left lType
    rEqns <- judge right rType
    let newEqn = TypeEqn
            (TyVar () lType, TyArr () (TyVar () rType) (TyVar () qType))
    return (TypeExist [rType, lType] (newEqn : lEqns : [rEqns]))

judge (FFix t) fType = do
    (counter, _) <- get
    tType        <- newTypeVar
    tEqns        <- judge t tType
    let newEqn = TypeEqn
            (TyVar () tType, TyArr () (TyVar () fType) (TyVar () fType))
    return (TypeExist [tType] (newEqn : [tEqns]))

judge (Pair p1 p2) pType = do
    (counter, _) <- get
    p1Type       <- newTypeVar
    p2Type       <- newTypeVar
    p1Eqns       <- judge p1 p1Type
    p2Eqns       <- judge p2 p2Type
    let newEqn =
            TypeEqn
                ( TyVar () pType
                , TyProduct () (TyVar () p1Type) (TyVar () p2Type)
                )
    return (TypeExist [p1Type, p2Type] (newEqn : p1Eqns : [p2Eqns]))

judge (PCase t ((x, y), s)) qType = do
    (counter, context) <- get
    tType              <- newTypeVar
    xType              <- newTypeVar
    yType              <- newTypeVar
    tEqns              <- judge t tType
    setContext $ [(x, xType), (y, yType)] ++ context
    sEqns <- judge s qType
    setContext context
    let newEqn =
            TypeEqn
                (TyVar () tType, TyProduct () (TyVar () xType) (TyVar () yType))
    return (TypeExist [xType, yType, tType] (newEqn : tEqns : [sEqns]))

judge Unit uType = do
    return (TypeEqn (TyVar () uType, TyUnit ()))

judge (UCase t s) qType = do
    (counter, _) <- get
    tType        <- newTypeVar
    tEqns        <- judge t tType
    sEqns        <- judge s qType
    let newEqn = TypeEqn (TyVar () tType, TyUnit ())
    return (TypeExist [tType] (newEqn : tEqns : [sEqns]))

judge Zero zType = do
    return (TypeEqn (TyVar () zType, TyNat ()))

judge Succ sType = do
    return (TypeEqn (TyVar () sType, TyArr () (TyNat ()) (TyNat ())))

judge (NCase t t0 (n, t1)) qType = do
    (counter, context) <- get
    tType              <- newTypeVar
    t0Type             <- newTypeVar
    nType              <- newTypeVar
    t1Type             <- newTypeVar
    tEqns              <- judge t tType
    t0Eqns             <- judge t0 t0Type
    setContext $ (n, nType) : context
    t1Eqns <- judge t1 t1Type
    setContext context
    let newEqns =
            [ TypeEqn (TyVar () tType, TyNat ())
            , TypeEqn (TyVar () t0Type, TyVar () qType)
            , TypeEqn (TyVar () nType, TyNat ())
            , TypeEqn (TyVar () t1Type, TyVar () qType)
            ]
    return
        (TypeExist [tType, t0Type, nType, t1Type]
                   (newEqns ++ [tEqns] ++ [t0Eqns] ++ [t1Eqns])
        )

judge Nil qType = do
    aType <- newTypeVar
    return
        (TypeExist [aType]
                   [TypeEqn (TyVar () qType, TyList () (TyVar () aType))]
        )

judge Cons qType = do
    aType <- newTypeVar
    return
        (TypeExist
            [aType]
            [ TypeEqn
                  ( TyVar () qType
                  , TyArr
                      ()
                      (TyProduct ()
                                 (TyVar () aType)
                                 (TyList () (TyVar () aType))
                      )

                      (TyList () (TyVar () aType))
                  )
            ]
        )

judge (LCase t t0 (v, t1)) qType = do
    (counter, context) <- get
    tType              <- newTypeVar
    t0Type             <- newTypeVar
    vType              <- newTypeVar
    t1Type             <- newTypeVar
    xType              <- newTypeVar
    tEqns              <- judge t tType
    t0Eqns             <- judge t0 t0Type
    setContext ((v, vType) : context)
    t1Eqns <- judge t1 t1Type
    setContext context
    let
        newEqns =
            [ TypeEqn (TyVar () tType, TyList () (TyVar () xType))
            , TypeEqn (TyVar () t0Type, TyVar () qType)
            , TypeEqn
                ( TyVar () vType
                , TyProduct () (TyVar () xType) (TyList () (TyVar () xType))
                )
            , TypeEqn (TyVar () t1Type, TyVar () qType)
            ]
    return
        (TypeExist [xType, tType, vType, t0Type, t1Type]
                   (newEqns ++ [tEqns] ++ [t0Eqns] ++ [t1Eqns])
        )