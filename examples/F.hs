{-# LANGUAGE DeriveGeneric,
             DeriveDataTypeable,
             FlexibleInstances,
             FlexibleContexts,
             MultiParamTypeClasses,
             ScopedTypeVariables
  #-}

module F where

import Unbound.Generics.LocallyNameless

import GHC.Generics
import Data.Typeable (Typeable)

import Control.Monad.Identity
import Control.Monad.Trans.Error
import Data.List as List


-- System F with type and term variables

type TyName = Name Ty
type TmName = Name Tm

data Ty = TyVar TyName
        | Arr Ty Ty
        | All (Bind TyName Ty)
   deriving (Show, Generic, Typeable)

data Tm = TmVar TmName
        | Lam (Bind (TmName, Embed Ty) Tm)
        | TLam (Bind TyName Tm)
        | App Tm Tm
        | TApp Tm Ty
   deriving (Show, Generic, Typeable)

------------------------------------------------------
instance Alpha Ty
instance Alpha Tm

instance Subst Tm Ty
instance Subst Tm Tm where
  isvar (TmVar v) = Just (SubstName v)
  isvar _  = Nothing

instance Subst Ty Ty where
  isvar (TyVar v) = Just (SubstName v)
  isvar _ = Nothing

------------------------------------------------------
-- Example terms
------------------------------------------------------

x :: Name Tm
y :: Name Tm
z :: Name Tm
(x,y,z) = (string2Name "x", string2Name "y", string2Name "z")

a :: Name Ty
b :: Name Ty
c :: Name Ty
(a,b,c) = (string2Name "a", string2Name "b", string2Name "c")

-- /\a. \x:a. x
polyid :: Tm
polyid = TLam (bind a (Lam (bind (x, Embed (TyVar a)) (TmVar x))))

-- All a. a -> a
polyidty :: Ty
polyidty = All (bind a (Arr (TyVar a) (TyVar a)))

-- /\b. \y:b. y
polyid2 :: Tm
polyid2 = TLam (bind b (Lam (bind (y, Embed (TyVar b)) (TmVar y))))

-- /\c. \y:b. y
bad_polyid2 :: Tm
bad_polyid2 = TLam (bind c (Lam (bind (y, Embed (TyVar b)) (TmVar y))))


-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------
type Delta = [ TyName ]
type Gamma = [ (TmName, Ty) ]

data Ctx = Ctx { getDelta :: Delta , getGamma :: Gamma }
           deriving (Show)
                    
emptyCtx :: Ctx
emptyCtx = Ctx { getDelta = [], getGamma = [] }

type M = ErrorT String (FreshMT Identity)

runM :: M a -> a
runM m = case (runIdentity $ runFreshMT (runErrorT m)) of
   Left s  -> error s
   Right ans -> ans

checkTyVar :: Ctx -> TyName -> M ()
checkTyVar g v = do
    if List.elem v (getDelta g) then
      return ()
    else
      throwError $ "NotFound: " ++ show v ++ " in " ++ show g

lookupTmVar :: Ctx -> TmName -> M Ty
lookupTmVar g v = do
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwError "NotFound"

extendTy :: TyName -> Ctx -> Ctx
extendTy n ctx = ctx { getDelta =  n : (getDelta ctx) }

extendTm :: TmName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : (getGamma ctx) }

tcty :: Ctx -> Ty -> M ()
tcty g  (TyVar alpha) =
   checkTyVar g alpha
tcty g  (All bnder) = do
   (alpha, ty') <- unbind bnder
   tcty (extendTy alpha g) ty'
tcty g  (Arr t1 t2) = do
   tcty g  t1
   tcty g  t2

ti :: Ctx -> Tm -> M Ty
ti g (TmVar v) = lookupTmVar g v
ti g (Lam bnd) = do
  ((v, Embed ty1), t) <- unbind bnd
  tcty g ty1
  ty2 <- ti (extendTm v ty1 g) t
  return (Arr ty1 ty2)
ti g (App t1 t2) = do
  ty1 <- ti g t1
  ty2 <- ti g t2
  case ty1 of
    Arr ty11 ty21 | ty2 `aeq` ty11 ->
      return ty21
    _ -> throwError "TypeError"
ti g (TLam bnd) = do
  (v, t) <- unbind bnd
  ty <- ti (extendTy v g) t
  return (All (bind v ty))
ti g (TApp t ty) = do
  tyt <- ti g t
  case tyt of
   (All bnder) -> do
      tcty g  ty
      (n1, ty1) <- unbind bnder
      return $ subst n1 ty ty1
   _ -> throwError $ "Expected a ForAll in a type application, got " ++ show tyt


