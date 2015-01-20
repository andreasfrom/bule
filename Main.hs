{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

-- Inspired by https://github.com/shayan-najd/MiniFeldspar/blob/master/Philip/GADT.hs

-- This is an attempt at specifying a correct-by-construction AST with accompanying
-- functions for running the code and inspecting the type.
-- Everything needs more work, especially Data and Case

module Main where

import           Data.Proxy
import           GHC.TypeLits
import           Unsafe.Coerce (unsafeCoerce)

deriving instance Show (Kind k)
deriving instance (Show payload, Show poly) => Show (Data typ poly payload)

-- Derive instance manually to print the type-level symbols
instance Show (Typ a) where
  show TInt = "Int"
  show TBool = "Bool"
  show TString = "String"
  show (a :-> b) = show a ++ " -> " ++ show b
  show TVar = "var"
  show TUnit = "()"
  show (TTuple a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (TKind k) = "(" ++ show k ++ ")"
  show (TData typ poly) = "Data " ++ symbolVal typ ++ " " ++ show poly

data Kind a where
  None :: Kind ()
  One :: Typ a -> Kind a
  Inc :: Typ a -> Kind b -> Kind (b, a)

data Var e a where
  Z :: Var (e,a) a
  S :: Var e a -> Var (e,b) a

infixr :->
infixr `Lam`

data Data (typ :: Symbol) (poly :: *)  payload = MkData String payload

data Exp e a where
  EInt :: Int -> Exp e Int
  EBool :: Bool -> Exp e Bool
  EString :: String -> Exp e String
  Var :: Var e a -> Exp e a
  Lam :: Exp e a -> Exp (e,a) b -> Exp e (a -> b)
  App :: Exp e (a -> b) -> Exp e a -> Exp e b
  If :: Exp e Bool -> Exp e a -> Exp e a -> Exp e a
  Let :: Exp (e,b) b -> Exp (e,b) a -> Exp e a
  Type :: Typ a -> Exp e a
  Interop :: Exp e a -> String -> a -> Exp e a

  EUnit :: Exp e ()
  ETuple :: Exp e a -> Exp e b -> Exp e (a,b)
  EFst :: Exp e (a,b) -> Exp e a
  ESnd :: Exp e (a,b) -> Exp e b

  -- Problem: Can't figure out how to return a specific type when chk'ing this
  CData :: KnownSymbol typ =>
           Exp e (Data typ kind payload) ->
           String -> Exp (e, kind) (poly, payload) ->
           Exp e (payload -> Data typ poly payload)

  -- Problem: Requires unsafeCoerce when running
  Case :: Exp e (Data typ poly payload) -> CaseList typ poly e ret -> Exp e ret

data Typ a where
  TInt :: Typ Int
  TBool :: Typ Bool
  TString :: Typ String
  (:->) :: Typ a -> Typ b -> Typ (a -> b)
  TVar :: Typ t
  TUnit :: Typ ()
  TTuple :: Typ a -> Typ b -> Typ (a,b)
  TKind :: Kind kind -> Typ kind
  TData :: KnownSymbol typ => Proxy typ -> Typ poly -> Typ (Data typ poly payload)

data CaseList typ poly e ret where
  Nil :: CaseList typ poly e ret
  Cons ::
    ( Exp e (payload -> Data typ poly payload)
    , Exp (e, payload) ret
    ) ->
    CaseList typ poly e ret ->
    CaseList typ poly e ret

data Env e where
  Empty :: Env ()
  Extend :: Env e -> Typ a -> Env (e,a)

get :: Var e a -> e -> a
get Z     (_ ,x) = x
get (S n) (xs,_) = get n xs

gets :: Var e a -> Env e -> Typ a
gets Z     (Extend _ x)  = x
gets (S n) (Extend xs _) = gets n xs
gets _     Empty         = error "Type fail!"

-- Every error in the below run and chk functions are considered deficiencies

run :: Exp e a -> e -> a
run (EInt i)      _ = i
run (EBool b)     _ = b
run (EString s)   _ = s
run (Var x)       r = get x r
run (Lam _ eb)    r = \v -> run eb (r,v)
run (App ef ea)   r = run ef r $ run ea r
run (If cond t e) r = if run cond r then run t r else run e r
run (Let x y)     r = let r' = run x (r, r') in run y (r, r')
run (Interop _ _ f) _ = f
run (Type _)      _ = error "run Type"
run EUnit         _ = ()
run (ETuple a b)  r = (run a r, run b r)
run (EFst t)    r = fst $ run t r
run (ESnd t)    r = snd $ run t r
run (CData _ s _) _ = \a -> MkData s a
run (Case _ Nil) _ = error "Pattern match(es) are non-exhaustive"
run (Case x (Cons (c,f) l)) r =
  let (MkData con payload) = run x r in
   case run (App c undefined) r of
    MkData con' _ ->
      if con ==  con'
      then run f (r, unsafeCoerce payload)
      else run (Case x l) r

chk :: Exp e a -> Env e -> Typ a
chk (EInt _)    _ = TInt
chk (EBool _)   _ = TBool
chk (EString _) _ = TString
chk (Var x)     r = gets x r
chk (Lam ta eb) r = chk ta r :-> chk eb (r `Extend` chk ta r)
chk (App ef _)  r = case chk ef r of
  _ :-> tr -> tr
  TVar -> error "chk App TVar"
  TKind _ -> error "chk App TKind"
chk (If _ t _)  r = chk t r
chk (Let x y)   r = let r' = chk x (r `Extend` r') in chk y (r `Extend` chk x (r `Extend` r'))
chk (Interop ty _ _) r = chk ty r
chk (Type t)    _ = t
chk EUnit       _ = TUnit
chk (ETuple a b) r = chk a r `TTuple` chk b r
chk (EFst t)    r = case chk t r of
  TTuple a _ -> a
  TVar -> error "chk EFst TVar"
  TKind _ -> error "chk EFst TKind"
chk (ESnd t)    r = case chk t r of
  TTuple _ b -> b
  TVar -> error "chk ESnd TVar"
  TKind _ -> error "chk ESnd TKind"
chk (CData dat _ t) r = case chk dat r of
  TData typ kind ->
    case chk t (r `Extend` kind) of
     TTuple poly payload -> payload :-> TData typ poly -- This type isn't really useful, it's TVar instead of something specific
     TVar -> error "chk CData TVar"
     TKind _ -> error "chk CData TKind"
  TVar -> error "chk CData TVar"
  TKind _ -> error "chk CData TKind"

chk (Case _ Nil) _ = error "Pattern match(es) are non-exhaustive"
chk (Case _ (Cons (_,_) _)) _ = error "chk Case"

-- Helper functions

app2 :: Exp e (a -> b -> c) -> Exp e a -> Exp e b -> Exp e c
app2 f x y = App (App f x) y

app3 :: Exp e (a -> b -> c -> d) -> Exp e a -> Exp e b -> Exp e c -> Exp e d
app3 f x y z = App (app2 f x y) z

app4 :: Exp e (a -> b -> c -> d -> x) -> Exp e a -> Exp e b -> Exp e c -> Exp e d -> Exp e x
app4 f x y z a = App (app3 f x y z) a

-- Experiments

plus' :: Exp e (Int -> Int -> Int)
plus' = Interop (Type (TInt :-> TInt :-> TInt)) "(+)" (+)

minus' :: Exp e (Int -> Int -> Int)
minus' = Interop (Type (TInt :-> TInt :-> TInt)) "(-)" (-)

lt' :: Exp e (Int -> Int -> Bool)
lt' = Interop (Type (TInt :-> TInt :-> TBool)) "(<)" (<)

eq' :: Eq a => Exp e (a -> a -> a -> Bool)
eq' = Lam (Type TVar) (Interop ((Var Z) `Lam` (Var (S Z) `Lam` Type TBool)) "(==)" (==))

expr' :: Exp e (a -> (a -> a) -> a -> a)
expr' = Lam (Type TVar) (Lam (Var Z `Lam` Var Z) (Lam (Var (S Z)) (App (Var (S Z)) (Var Z))))

rec' :: Exp (e,a) a -> Exp e a
rec' f = Let f (Var Z)

gcd' :: Exp e (Int -> Int -> Int)
gcd' = rec' $
       Lam (Type TInt)
       (Lam (Type TInt)
        (If (app3 eq' (Type TInt) (Var Z) (EInt 0))
         (Var (S Z))
         (If (app2 lt' (Var (S Z)) (Var Z))
          (app2 (Var (S (S Z))) (Var Z) (Var (S Z)))
          (app2 (Var (S (S Z))) (app2 minus' (Var (S Z)) (Var Z)) (Var Z)))))

flip' :: Exp e (a -> b -> c -> (a -> b -> c) -> b -> a -> c)
flip' = Lam (Type TVar)
        (Lam (Type TVar)
         (Lam (Type TVar)
          (Lam (Var (S (S Z)) `Lam` (Var (S (S Z))) `Lam` (Var (S (S Z))))
           (Lam (Var (S (S Z)))
            (Lam (Var (S (S (S (S Z)))))
             (App
              (App (Var (S (S Z))) (Var Z))
              (Var (S Z))))))))

and' :: Exp e (Bool -> Bool -> Bool)
and' = Interop (Type (TBool :-> TBool :-> TBool)) "(&&)" (&&)

mul' :: Exp e (Int -> Int -> Int)
mul' = Interop (Type (TInt :-> TInt :-> TInt)) "(*)" (*)

abs' :: Exp e (Int -> Int)
abs' = Lam (Type TInt)
       (If (app2 lt' (Var Z) (EInt 0))
        (app2 mul' (Var Z) (EInt (-1)))
        (Var Z))

letTest' :: Exp e Bool
letTest' = Let (Interop (Type (TBool :-> TBool)) "not" not)
           (App (Var Z) (EBool False))

fact' :: Exp e (Int -> Int)
fact' = rec' $
        Lam (Type TInt)
        (If (app3 eq' (Type TInt) (Var Z) (EInt 0))
         (EInt 1)
         (app2 mul' (Var Z) (App (Var (S Z))
                             (app2 minus' (Var Z) (EInt 1)))))

-- Data (needs work)

maybe' :: Exp e (Data "Maybe" k payload)
maybe' = Type $ TData (Proxy :: Proxy "Maybe") (TKind (One TVar))

just' :: Exp e (payload -> Data "Maybe" payload payload)
just' = CData maybe' "Just" (ETuple (Var Z) (Var Z))

nothing' :: Exp e (() -> Data "Maybe" poly ())
nothing' = CData maybe' "Nothing" (ETuple (Var Z) (Type TUnit))

pair' :: Exp e (Data "Pair" (j, k) payload)
pair' = Type $ TData (Proxy :: Proxy "Pair") (TKind (Inc TVar (One TVar)))

mkPair' :: Exp e ((a,b) -> Data "Pair" (a,b) (a,b))
mkPair' = CData pair' "MkPair" (ETuple (Var Z) (Var Z))

either' :: Exp e (Data "Either" (k,i) payload)
either' = Type $ TData (Proxy :: Proxy "Either") (TKind (Inc TVar (One TVar)))

left' :: Exp e (a -> Data "Either" (a,b) a)
left' = CData either' "Left" (ETuple (Var Z) (EFst (Var Z)))

right' :: Exp e (b -> Data "Either" (a,b) b)
right' = CData either' "Right" (ETuple (Var Z) (ESnd (Var Z)))

-- Case (needs work)

caseList :: CaseList "Maybe" Int e Int
caseList =
  (Cons (just', Var Z)
    (Cons (nothing', EInt 5) Nil))

as1', as2' :: Exp e Int
as1' = Case (App just' (EInt 10)) caseList
as2' = Case (App nothing' EUnit) caseList
