> {-# LANGUAGE 
>   GADTs, 
>   KindSignatures, 
>   DataKinds #-}

> module Main where

> import Control.Applicative
> import Control.Monad.Error

> data Dir = Check | Infer

> data Term :: Dir -> * where
>   Ann :: Term Check -> Type -> Term Infer
>   Bound :: Int -> Term Infer
>   Free :: Name -> Term Infer
>   (:@:) :: Term Infer -> Term Check -> Term Infer
>   -----------------------------------------------
>   Lam :: Term Check -> Term Check
>   Inf :: Term Infer -> Term Check

> data Name 
>     = Global String
>     | Local Int
>     | Quote Int
>       deriving Eq

Types:

> data Atoms 
>     = Nat
>     | Bool

> data Type 
>     = TFree Name
>     | Arr Type Type
>     | Atom Atoms

STLC Model in Haskell:

> data Value 
>     = VLam (Value -> Value)
>     | VNeu Neutral

> data Neutral
>     = VFree Name
>     | NApp Neutral Value

\n . suc  (suc (n))

Denotation:

> type Env = [Value]

> evalCheck :: Term Check -> Env -> Value
> evalCheck (Lam b) env = VLam  $ \ s -> evalCheck b (s : env)
> evalCheck (Inf tm) env = evalInfer tm env

> evalInfer :: Term Infer -> Env -> Value
> evalInfer (Bound n) env    = env !! n
> evalInfer (Free v) env     = VNeu (VFree v)
> evalInfer (f :@: s) env    = 
>     case vf of
>       VLam f -> f vs
>       VNeu n -> VNeu (NApp n vs)
>     where vf = evalInfer f env
>           vs = evalCheck s env
> evalInfer (Ann tm ty) env  = evalCheck tm env

Context:

> data Kind = Star

> data Info
>     = HasType Type
>     | HasKind Kind

> type Context = [(Name, Info)]

> initCtxt = [("Nat", HasKind Star),("ze", HasType Nat)]

Type cheking

> type Checker a = Either String a

> kindCheck :: Context -> Type -> Kind -> Checker ()
> kindCheck ctx (TFree x) Star =
>     case x `lookup` ctx of
>       Just (HasKind Star) -> return ()
>       Nothing -> throwError "Unknown type variable"
> kindCheck ctx (Arr ty ty') Star = do
>   kindCheck ctx ty Star
>   kindCheck ctx ty' Star