module Lib.AST where

import Data.List
import Control.Monad
import Lib.Monads

import Data.Traversable
import Data.Foldable
import Control.Applicative

{- AST.hs
 - This file includes the data type of the AST of the lambda terms and types you should use.
 -
 - Moreover, this includes the functions ``termPrettyShow`` and ``tyTermPrettyShow`` for pretty showing
 - the data type of the lambda term and a type of a lambda term.
 -}

-- | Type alias for a lambda term
type LambdaTerm = Term String String

-- | The type of a term 
data Term abs var
    -- | Variable
    = Var var
    -- | Abstraction 
    | Abs abs (Term abs var)
    -- | Application
    | App (Term abs var) (Term abs var)
    -- | Built in fixed point combinator
    -- The type of this primitive function can be thought of as having type: (a -> a) -> a
    | FFix (Term abs var)
    -- | Pair is a tuple. 
    | Pair (Term abs var) (Term abs var)
    -- | Case for products
    | PCase 
        (Term abs var)                   -- Term to case on.. 
        ((String, String), Term abs var) -- pattern match i.e., we would write (a,b) -> t where t is a term
    -- | Unit is for the unit type. In Haskell this is ``()``
    | Unit 
    -- | Case for the unit 
    | UCase
        (Term abs var)           -- Term to case on.. 
        (Term abs var)           -- pattern match i.e., () -> t where t is a term

    {- The natural numbers in this language roughly correspond to the following Haskell definition
     -          data Nat 
     -              = Succ Nat
     -              | Zero
     -}
    -- | Succ
    -- The type of this primitive function can be thought of as having type: Nat -> Nat
    | Succ                      -- Primitive Succ function for naturals
    -- | Zero
    -- The type of this primitive function can be thought of as having type: Nat
    | Zero                      -- Primitive Zero function for naturals

    -- | Natural number case
    | NCase
        (Term abs var)          -- Term to case on
        (Term abs var)          -- Zero case i.e., we would write Zero -> t where t is a term
        (abs, Term abs var)     -- Succ case i.e., we would write Succ n -> t where t is the term 

    {- The lists in this language roughly correspond to the following Haskell definition
     -          data [a]
     -              = Cons (a, [a])
     -              | Nil
     - Note how ``Cons`` takes in a tuple.
     -}
    -- | Cons
    -- The type of this primitive function can be thought of as having type: (a, [a]) -> [a]
    | Cons                      -- Primitive Cons function for lists
    -- | Nil
    -- The type of this primitive function can be thought of as having type: [a]
    | Nil                       -- Primitive Nil function for lists
    -- | List case
    | LCase 
        (Term abs var)          -- Term to case on
        (Term abs var)          -- Nil case i.e., we would write Nil -> t where t is a term
        (abs, Term abs var)     -- Cons case i.e., we would write Cons v -> t where t is a term
  deriving (Show, Eq)

-- | Type for the type of a lambda term
type LambdaTyTerm = TyTerm () String

-- | Type for a type of a lambda term.
-- There is some explanation needed here for the type variables...
--      - ``ann`` is the "annotation" of a TyTerm, for example, if you want to store extra information 
--          in a TyTerm, you can instantiate ``ann`` with any type you want.
--          This is helpful for reporting better error messages for example (to keep track of which
--          lambda term the type should be associated to!).
--     - ``var`` is the type for which variables will be represented.
data TyTerm ann var
    -- | Type variable
    = TyVar ann var
    -- | Type arrow i.e., this is the type (->) in Haskell i.e., a function type
    | TyArr ann (TyTerm ann var) (TyTerm ann var)
    -- | Type product i.e., this is the type (,) in Haskell i.e., a tuple type
    | TyProduct ann (TyTerm ann var) (TyTerm ann var)
    -- | Type natural i.e., this is a natural number type
    | TyNat ann
    -- | Type unit i.e.,, this is the type () in Haskell
    | TyUnit ann
    -- | Type list i.e., this is a list data type i.e., this is the type [] in Haskell
    | TyList ann (TyTerm ann var)
  deriving (Show, Eq)

-- | This function is used to pretty print a Lambda Term
-- It simply specializes the type of the type class below.
lambdaTermPrettyShow :: LambdaTerm -> String
lambdaTermPrettyShow = termPrettyShow

-- | This function is used to pretty print the type of a 
-- lambda term.
-- It simply specializes the type of the type class below.
lambdaTyPrettyShow :: LambdaTyTerm -> String
lambdaTyPrettyShow = tyTermPrettyShow

-------------------------
-- Everything past here you can ignore... 
-- This just includes the pretty printers, internal utility functions, Functor,
-- Foldable, and Traversable instances of TyTerm and Term which are not
-- necessary to complete the assignment...
-------------------------

-- | This type class is used to pretty print a term
class TermPrettyShow a where
    termPrettyShow :: a -> String

instance TermPrettyShow Char where
    termPrettyShow = pure

instance TermPrettyShow a => TermPrettyShow [a] where
    termPrettyShow = concatMap termPrettyShow

instance (TermPrettyShow abs, TermPrettyShow var) => TermPrettyShow (Term abs var) where
    termPrettyShow = go
      where
        go term = case term of
            Var v -> termPrettyShow v
            Abs abs bdy -> concat [ "\\", termPrettyShow abs, " -> ", go bdy]
            App l r -> l' ++ " " ++ r'               
              where
                r' = case r of  
                    Abs _ _ -> r''
                    FFix _ -> r''
                    PCase _ _ -> r''
                    UCase _ _ -> r''
                    NCase _ _ _ -> r''
                    LCase _ _ _ -> r''
                    App _ _ -> r''
                    _ -> go r
                r'' = concat ["(", go r, ")"]

                l' = case l of
                    Abs _ _ -> l''
                    PCase _ _ -> l''
                    UCase _ _ -> l''
                    NCase _ _ _ -> l''
                    LCase _ _ _ -> l''
                    _ -> go l
                l'' = concat ["(", go l, ")"]

            FFix t -> concat ["fix ", t']
              where
                t' = case t of
                    Abs _ _ -> t''
                    FFix _ -> t''
                    PCase _ _ -> t''
                    UCase _ _ -> t''
                    NCase _ _ _ -> t''
                    LCase _ _ _ -> t''
                    App _ _ -> t''
                    _ -> go t
                t'' = concat ["(", go t, ")"]

            Pair l r -> concat ["(", go l,", ", go r,")"]
            PCase caseon ((a,b), bdy) -> concat 
                [ "case "
                , go caseon
                , " of "
                , "("
                , termPrettyShow a
                , ", "
                , termPrettyShow b
                , ")"
                , " -> "
                , go bdy
                ] 
            Unit -> "()"
            UCase caseon bdy -> concat
                [ "case "
                , go caseon
                , " of "
                , "("
                , ")"
                , " -> "
                , go bdy
                ] 
            Succ ->  "Succ"
            Zero ->  "Zero"
            NCase caseon zcase (a, ncase) -> concat
                [ "case "
                , go caseon
                , " of "
                , "Zero -> "
                , go zcase
                , " ; "
                , "Succ "
                , termPrettyShow a
                , " -> "
                , go ncase
                ] 

            Cons -> "Cons"
            Nil -> "Nil"

            LCase caseon ncase (a, ccase) -> concat
                [ "case "
                , go caseon
                , " of "
                , "Nil -> "
                , go ncase
                , " ; "
                , "Cons "
                , termPrettyShow a
                , " -> "
                , go ccase
                ] 

-- | This type class is used to pretty print the type of a term
class TyTermPrettyShow a where
    tyTermPrettyShow :: a -> String

instance TyTermPrettyShow Char where
    tyTermPrettyShow = pure

instance TyTermPrettyShow Int where
    tyTermPrettyShow = show

instance TyTermPrettyShow a => TyTermPrettyShow [a] where
    tyTermPrettyShow = concatMap tyTermPrettyShow

instance TyTermPrettyShow var => TyTermPrettyShow (TyTerm ann var) where
    tyTermPrettyShow = go
      where
        go ty = case ty of
            TyVar _ a -> tyTermPrettyShow a
            TyArr _ (TyArr _ l' r') r  -> concat 
                [ "("
                , go l'
                , " -> "
                , go r'
                , ")"
                , " -> "
                , go r
                ]
            TyArr _ l r -> concat [ go l , " -> " , go r ]
            TyProduct _ l r -> concat [ "(" , go l, ", ", go r, ")" ]
            TyNat _ -> "Nat"
            TyList _ a -> concat ["[", go a, "]"]
            TyUnit _ -> "()"

-- | This function is used to get the top level annotation of
-- a type
tyAnn :: TyTerm ann var -> ann
tyAnn ty = case ty of
    TyVar ann _ -> ann
    TyArr ann _ _ -> ann
    TyProduct ann _ _ -> ann
    TyNat ann -> ann
    TyUnit ann -> ann
    TyList ann _ -> ann

termChildren :: Term abs var -> [Term abs var]
termChildren t = case t of
    Var v -> []
    Abs _ bdy -> [bdy]
    App l r -> [l,r]
    FFix bdy -> [bdy]
    Pair l r -> [l,r]
    PCase caseon (_, res) -> [caseon, res]
    Unit -> []
    UCase caseon res -> [caseon, res]
    Succ -> []
    Zero -> []
    NCase caseon z (_, s) -> [caseon,z,s]
    Cons -> []
    Nil -> []
    LCase caseon n (_, c) -> [caseon,n,c]

instance Functor (Lib.AST.Term abs) where
    fmap f_a2If (Lib.AST.Var a1_a2Ig)
      = Lib.AST.Var (f_a2If a1_a2Ig)
    fmap f_a2Ih (Lib.AST.Abs a1_a2Ii a2_a2Ij)
      = Lib.AST.Abs
          ((\ b1_a2Ik -> b1_a2Ik) a1_a2Ii) (fmap f_a2Ih a2_a2Ij)
    fmap f_a2Il (Lib.AST.App a1_a2Im a2_a2In)
      = Lib.AST.App
          (fmap f_a2Il a1_a2Im) (fmap f_a2Il a2_a2In)
    fmap f_a2Io (Lib.AST.FFix a1_a2Ip)
      = Lib.AST.FFix (fmap f_a2Io a1_a2Ip)
    fmap f_a2Iq (Lib.AST.Pair a1_a2Ir a1_a2Il)
      = Lib.AST.Pair (fmap f_a2Iq a1_a2Ir) (fmap f_a2Iq a1_a2Il)
    fmap f_a2Iv (Lib.AST.PCase a1_a2Iw a2_a2Ix)
      = Lib.AST.PCase
          (fmap f_a2Iv a1_a2Iw)
          ((\ b2_a2Iy
              -> case b2_a2Iy of {
                   ((,) a1_a2Iz a2_a2IA)
                     -> (,)
                          ((\ b1_a2IB -> b1_a2IB) a1_a2Iz) (fmap f_a2Iv a2_a2IA) })
             a2_a2Ix)
    fmap f_a2IC Lib.AST.Unit = Lib.AST.Unit
    fmap f_a2ID (Lib.AST.UCase a1_a2IE a2_a2IF)
      = Lib.AST.UCase
          (fmap f_a2ID a1_a2IE) (fmap f_a2ID a2_a2IF)
    fmap f_a2IG Lib.AST.Succ = Lib.AST.Succ
    fmap f_a2IH Lib.AST.Zero = Lib.AST.Zero
    fmap f_a2II (Lib.AST.NCase a1_a2IJ a2_a2IK a3_a2IL)
      = Lib.AST.NCase
          (fmap f_a2II a1_a2IJ) (fmap f_a2II a2_a2IK)
          ((\ b2_a2IM
              -> case b2_a2IM of {
                   ((,) a1_a2IN a2_a2IO)
                     -> (,)
                          ((\ b1_a2IP -> b1_a2IP) a1_a2IN) (fmap f_a2II a2_a2IO) })
             a3_a2IL)
    fmap f_a2IQ Lib.AST.Cons = Lib.AST.Cons
    fmap f_a2IR Lib.AST.Nil = Lib.AST.Nil
    fmap f_a2IS (Lib.AST.LCase a1_a2IT a2_a2IU a3_a2IV)
      = Lib.AST.LCase
          (fmap f_a2IS a1_a2IT) (fmap f_a2IS a2_a2IU)
          ((\ b2_a2IW
              -> case b2_a2IW of {
                   ((,) a1_a2IX a2_a2IY)
                     -> (,)
                          ((\ b1_a2IZ -> b1_a2IZ) a1_a2IX) (fmap f_a2IS a2_a2IY) })
             a3_a2IV)

instance Foldable (Lib.AST.Term abs) where
    foldMap f_a2Lh (Lib.AST.Var a1_a2Li) = f_a2Lh a1_a2Li
    foldMap f_a2Lj (Lib.AST.Abs a1_a2Lk a2_a2Ll)
      = foldMap f_a2Lj a2_a2Ll
    foldMap f_a2Lm (Lib.AST.App a1_a2Ln a2_a2Lo)
      = mappend
          (foldMap f_a2Lm a1_a2Ln)
          (foldMap f_a2Lm a2_a2Lo)
    foldMap f_a2Lp (Lib.AST.FFix a1_a2Lq)
      = foldMap f_a2Lp a1_a2Lq
    foldMap f_a2Lr (Lib.AST.Pair a1_a2Ls a1_a2Lt)
      = mappend (foldMap f_a2Lr a1_a2Ls) (foldMap f_a2Lr a1_a2Lt)
    foldMap f_a2Lw (Lib.AST.PCase a1_a2Lx a2_a2Ly)
      = mappend
          (foldMap f_a2Lw a1_a2Lx)
          ((\ b1_a2Lz
              -> case b1_a2Lz of {
                   ((,) a1_a2LA a2_a2LB) -> foldMap f_a2Lw a2_a2LB })
             a2_a2Ly)
    foldMap f_a2LC Lib.AST.Unit = mempty
    foldMap f_a2LD (Lib.AST.UCase a1_a2LE a2_a2LF)
      = mappend
          (foldMap f_a2LD a1_a2LE)
          (foldMap f_a2LD a2_a2LF)
    foldMap f_a2LG Lib.AST.Succ = mempty
    foldMap f_a2LH Lib.AST.Zero = mempty
    foldMap
      f_a2LI
      (Lib.AST.NCase a1_a2LJ a2_a2LK a3_a2LL)
      = mappend
          (foldMap f_a2LI a1_a2LJ)
          (mappend
             (foldMap f_a2LI a2_a2LK)
             ((\ b1_a2LM
                 -> case b1_a2LM of {
                      ((,) a1_a2LN a2_a2LO) -> foldMap f_a2LI a2_a2LO })
                a3_a2LL))
    foldMap f_a2LP Lib.AST.Cons = mempty
    foldMap f_a2LQ Lib.AST.Nil = mempty
    foldMap
      f_a2LR
      (Lib.AST.LCase a1_a2LS a2_a2LT a3_a2LU)
      = mappend
          (foldMap f_a2LR a1_a2LS)
          (mappend
             (foldMap f_a2LR a2_a2LT)
             ((\ b1_a2LV
                 -> case b1_a2LV of {
                      ((,) a1_a2LW a2_a2LX) -> foldMap f_a2LR a2_a2LX })
                a3_a2LU))

instance Traversable (Lib.AST.Term abs) where
    traverse f_a2Mq (Lib.AST.Var a1_a2Mr)
      = fmap (\ b1_a2Ms -> Lib.AST.Var b1_a2Ms) (f_a2Mq a1_a2Mr)
    traverse f_a2Mt (Lib.AST.Abs a1_a2Mu a2_a2Mv)
      = fmap
          (\ b2_a2Mw -> Lib.AST.Abs a1_a2Mu b2_a2Mw)
          (traverse f_a2Mt a2_a2Mv)
    traverse f_a2Mx (Lib.AST.App a1_a2My a2_a2Mz)
      = liftA2
          (\ b1_a2MA b2_a2MB -> Lib.AST.App b1_a2MA b2_a2MB)
          (traverse f_a2Mx a1_a2My)
          (traverse f_a2Mx a2_a2Mz)
    traverse f_a2MC (Lib.AST.FFix a1_a2MD)
      = fmap
          (\ b1_a2ME -> Lib.AST.FFix b1_a2ME)
          (traverse f_a2MC a1_a2MD)
    traverse f_a2MF (Lib.AST.Pair a1_a2MG a1_a2ML)
      = Lib.AST.Pair <$> traverse f_a2MF a1_a2MG <*> traverse f_a2MF a1_a2ML
    traverse f_a2MN (Lib.AST.PCase a1_a2MO a2_a2MP)
      = liftA2
          (\ b1_a2MQ b2_a2MR -> Lib.AST.PCase b1_a2MQ b2_a2MR)
          (traverse f_a2MN a1_a2MO)
          ((\ b1_a2MS
              -> case b1_a2MS of {
                   ((,) a1_a2MT a2_a2MU)
                     -> fmap
                          (\ b2_a2MV -> (,) a1_a2MT b2_a2MV)
                          (traverse f_a2MN a2_a2MU) })
             a2_a2MP)
    traverse f_a2MW Lib.AST.Unit
      = pure Lib.AST.Unit
    traverse f_a2MX (Lib.AST.UCase a1_a2MY a2_a2MZ)
      = liftA2
          (\ b1_a2N0 b2_a2N1 -> Lib.AST.UCase b1_a2N0 b2_a2N1)
          (traverse f_a2MX a1_a2MY)
          (traverse f_a2MX a2_a2MZ)
    traverse f_a2N2 Lib.AST.Succ
      = pure Lib.AST.Succ
    traverse f_a2N3 Lib.AST.Zero
      = pure Lib.AST.Zero
    traverse
      f_a2N4
      (Lib.AST.NCase a1_a2N5 a2_a2N6 a3_a2N7)
      = (<*>)
          (liftA2
             (\ b1_a2N8 b2_a2N9 b3_a2Na
                -> Lib.AST.NCase b1_a2N8 b2_a2N9 b3_a2Na)
             (traverse f_a2N4 a1_a2N5)
             (traverse f_a2N4 a2_a2N6))
          ((\ b1_a2Nb
              -> case b1_a2Nb of {
                   ((,) a1_a2Nc a2_a2Nd)
                     -> fmap
                          (\ b2_a2Ne -> (,) a1_a2Nc b2_a2Ne)
                          (traverse f_a2N4 a2_a2Nd) })
             a3_a2N7)
    traverse f_a2Nf Lib.AST.Cons
      = pure Lib.AST.Cons
    traverse f_a2Ng Lib.AST.Nil
      = pure Lib.AST.Nil
    traverse
      f_a2Nh
      (Lib.AST.LCase a1_a2Ni a2_a2Nj a3_a2Nk)
      = (<*>)
          (liftA2
             (\ b1_a2Nl b2_a2Nm b3_a2Nn
                -> Lib.AST.LCase b1_a2Nl b2_a2Nm b3_a2Nn)
             (traverse f_a2Nh a1_a2Ni)
             (traverse f_a2Nh a2_a2Nj))
          ((\ b1_a2No
              -> case b1_a2No of {
                   ((,) a1_a2Np a2_a2Nq)
                     -> fmap
                          (\ b2_a2Nr -> (,) a1_a2Np b2_a2Nr)
                          (traverse f_a2Nh a2_a2Nq) })
             a3_a2Nk)

        
instance Functor (Lib.AST.TyTerm ann) where
    fmap f_a3Dt (Lib.AST.TyVar a1_a3Du a2_a3Dv)
      = Lib.AST.TyVar ((\ b1_a3Dw -> b1_a3Dw) a1_a3Du) (f_a3Dt a2_a3Dv)
    fmap f_a3Dx (Lib.AST.TyArr a1_a3Dy a2_a3Dz a3_a3DA)
      = Lib.AST.TyArr
          ((\ b1_a3DB -> b1_a3DB) a1_a3Dy) (fmap f_a3Dx a2_a3Dz)
          (fmap f_a3Dx a3_a3DA)
    fmap f_a3DC (Lib.AST.TyProduct a1_a3DD a2_a3DE a3_a3DF)
      = Lib.AST.TyProduct
          ((\ b1_a3DG -> b1_a3DG) a1_a3DD) (fmap f_a3DC a2_a3DE)
          (fmap f_a3DC a3_a3DF)
    fmap f_a3DH (Lib.AST.TyNat a1_a3DI)
      = Lib.AST.TyNat ((\ b1_a3DJ -> b1_a3DJ) a1_a3DI)
    fmap f_a3DK (Lib.AST.TyUnit a1_a3DL)
      = Lib.AST.TyUnit ((\ b1_a3DM -> b1_a3DM) a1_a3DL)
    fmap f_a3DN (Lib.AST.TyList a1_a3DO a2_a3DP)
      = Lib.AST.TyList
          ((\ b1_a3DQ -> b1_a3DQ) a1_a3DO) (fmap f_a3DN a2_a3DP)
    (<$) z_a3DR (Lib.AST.TyVar a1_a3DS a2_a3DT)
      = Lib.AST.TyVar
          ((\ b1_a3DU -> b1_a3DU) a1_a3DS) ((\ b2_a3DV -> z_a3DR) a2_a3DT)
    (<$) z_a3DW (Lib.AST.TyArr a1_a3DX a2_a3DY a3_a3DZ)
      = Lib.AST.TyArr
          ((\ b1_a3E0 -> b1_a3E0) a1_a3DX) ((<$) z_a3DW a2_a3DY)
          ((<$) z_a3DW a3_a3DZ)
    (<$) z_a3E1 (Lib.AST.TyProduct a1_a3E2 a2_a3E3 a3_a3E4)
      = Lib.AST.TyProduct
          ((\ b1_a3E5 -> b1_a3E5) a1_a3E2) ((<$) z_a3E1 a2_a3E3)
          ((<$) z_a3E1 a3_a3E4)
    (<$) z_a3E6 (Lib.AST.TyNat a1_a3E7)
      = Lib.AST.TyNat ((\ b1_a3E8 -> b1_a3E8) a1_a3E7)
    (<$) z_a3E9 (Lib.AST.TyUnit a1_a3Ea)
      = Lib.AST.TyUnit ((\ b1_a3Eb -> b1_a3Eb) a1_a3Ea)
    (<$) z_a3Ec (Lib.AST.TyList a1_a3Ed a2_a3Ee)
      = Lib.AST.TyList
          ((\ b1_a3Ef -> b1_a3Ef) a1_a3Ed) ((<$) z_a3Ec a2_a3Ee)

instance Foldable (Lib.AST.TyTerm ann) where
    foldr f_a3Eg z_a3Eh (Lib.AST.TyVar a1_a3Ei a2_a3Ej)
      = f_a3Eg a2_a3Ej z_a3Eh
    foldr
      f_a3Ek
      z_a3El
      (Lib.AST.TyArr a1_a3Em a2_a3En a3_a3Eo)
      = (\ b1_a3Ep b2_a3Eq -> foldr f_a3Ek b2_a3Eq b1_a3Ep)
          a2_a3En
          ((\ b3_a3Er b4_a3Es -> foldr f_a3Ek b4_a3Es b3_a3Er)
             a3_a3Eo z_a3El)
    foldr
      f_a3Et
      z_a3Eu
      (Lib.AST.TyProduct a1_a3Ev a2_a3Ew a3_a3Ex)
      = (\ b1_a3Ey b2_a3Ez -> foldr f_a3Et b2_a3Ez b1_a3Ey)
          a2_a3Ew
          ((\ b3_a3EA b4_a3EB -> foldr f_a3Et b4_a3EB b3_a3EA)
             a3_a3Ex z_a3Eu)
    foldr f_a3EC z_a3ED (Lib.AST.TyNat a1_a3EE) = z_a3ED
    foldr f_a3EF z_a3EG (Lib.AST.TyUnit a1_a3EH) = z_a3EG
    foldr f_a3EI z_a3EJ (Lib.AST.TyList a1_a3EK a2_a3EL)
      = (\ b1_a3EM b2_a3EN -> foldr f_a3EI b2_a3EN b1_a3EM)
          a2_a3EL z_a3EJ
    foldMap f_a3EO (Lib.AST.TyVar a1_a3EP a2_a3EQ)
      = f_a3EO a2_a3EQ
    foldMap
      f_a3ER
      (Lib.AST.TyArr a1_a3ES a2_a3ET a3_a3EU)
      = mappend
          (foldMap f_a3ER a2_a3ET)
          (foldMap f_a3ER a3_a3EU)
    foldMap
      f_a3EV
      (Lib.AST.TyProduct a1_a3EW a2_a3EX a3_a3EY)
      = mappend
          (foldMap f_a3EV a2_a3EX)
          (foldMap f_a3EV a3_a3EY)
    foldMap f_a3EZ (Lib.AST.TyNat a1_a3F0)
      = mempty
    foldMap f_a3F1 (Lib.AST.TyUnit a1_a3F2)
      = mempty
    foldMap f_a3F3 (Lib.AST.TyList a1_a3F4 a2_a3F5)
      = foldMap f_a3F3 a2_a3F5

instance Traversable (Lib.AST.TyTerm ann) where
    traverse f_a3Fg (Lib.AST.TyVar a1_a3Fh a2_a3Fi)
      = fmap
          (\ b2_a3Fj -> Lib.AST.TyVar a1_a3Fh b2_a3Fj) (f_a3Fg a2_a3Fi)
    traverse
      f_a3Fk
      (Lib.AST.TyArr a1_a3Fl a2_a3Fm a3_a3Fn)
      = liftA2
          (\ b2_a3Fo b3_a3Fp -> Lib.AST.TyArr a1_a3Fl b2_a3Fo b3_a3Fp)
          (traverse f_a3Fk a2_a3Fm)
          (traverse f_a3Fk a3_a3Fn)
    traverse
      f_a3Fq
      (Lib.AST.TyProduct a1_a3Fr a2_a3Fs a3_a3Ft)
      = liftA2
          (\ b2_a3Fu b3_a3Fv -> Lib.AST.TyProduct a1_a3Fr b2_a3Fu b3_a3Fv)
          (traverse f_a3Fq a2_a3Fs)
          (traverse f_a3Fq a3_a3Ft)
    traverse f_a3Fw (Lib.AST.TyNat a1_a3Fx)
      = pure (Lib.AST.TyNat a1_a3Fx)
    traverse f_a3Fy (Lib.AST.TyUnit a1_a3Fz)
      = pure (Lib.AST.TyUnit a1_a3Fz)
    traverse f_a3FA (Lib.AST.TyList a1_a3FB a2_a3FC)
      = fmap
          (\ b2_a3FD -> Lib.AST.TyList a1_a3FB b2_a3FD)
          (traverse f_a3FA a2_a3FC)


