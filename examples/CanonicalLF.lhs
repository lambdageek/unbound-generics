Canonical LF
============

This is a representation of [LF](http://www.twelf.org/) in which all terms are
automatically in *canonical form*.  The key idea is to segregate the type families
and the terms into *atomic* and *normal* forms where the term variables only stand
for atomic terms, and not arbitrary ones.  Then, a substitution procedure is defined
that takes terms in normal form and performs a substitution for a variable while
simultaneously normalizing any redices that occur.

> {-# LANGUAGE DeriveGeneric, StandaloneDeriving, DeriveDataTypeable,
>     ViewPatterns, RankNTypes, FlexibleContexts #-}
> module CanonicalLF where
> import Unbound.Generics.LocallyNameless
> import GHC.Generics (Generic)
> import Data.Typeable (Typeable)
> import qualified Data.Map as M
> import Control.Monad.Reader
> import Data.Functor.Identity
> import Control.Applicative (Const(..))

> data Signature = NilS
>   | SnocAtom (Rebind Signature (Atm, Embed Kind))
>   | SnocConst (Rebind Signature (Cnst, Embed Type))
>   deriving (Show, Generic, Typeable)

> data Kind = TypeK | PiK (Bind (Var, Embed Type) Kind)
>   deriving (Show, Generic, Typeable)

> type Atm = Name P
> data P = AtmP Atm | AppP P Term
>   deriving (Show, Generic, Typeable)

> data Type = PT P | PiT (Bind (Var, Embed Type) Type)
>   deriving (Show, Generic, Typeable)

> type Cnst = Name R
> type Var = Name R
> data R = VarR Var | ConstR Cnst | AppR R Term
>   deriving (Show, Generic, Typeable)
> data Term = RM R | LamM (Bind Var Term)
>   deriving (Show, Generic, Typeable)

> data Context = NilC
>              | Snoc (Rebind Context (Var, Embed Type))
>              deriving (Show, Generic, Typeable)

> instance Alpha Signature
> instance Alpha Kind
> instance Alpha P
> instance Alpha Type
> instance Alpha R
> instance Alpha Term
> instance Alpha Context

> data SimpleType = AtmS Atm | ArrS SimpleType SimpleType
>   deriving (Show, Generic, Typeable)
>
> instance Alpha SimpleType

> isHeadVarR :: Var -> R -> Bool
> isHeadVarR x (VarR y) = x == y
> isHeadVarR _ (ConstR _) = False
> isHeadVarR x (AppR r _) = isHeadVarR x r

> data Spine a = NilSp a | AppSp (Spine a) Term
> data Head = VarH Var | ConstH Cnst

> headSpine :: Var -> R -> Either (Spine Head) (Spine ())
> headSpine x (VarR y) | x == y    = Right (NilSp ())
>                      | otherwise = Left (NilSp (VarH y))
> headSpine _ (ConstR c)           = Left (NilSp (ConstH c))
> headSpine x (AppR r m)           = case headSpine x r of
>   Left s -> Left (AppSp s m)
>   Right s -> Right (AppSp s m)

> substKind :: Fresh m => Term -> Var -> Kind -> m Kind
> substKind _ _ TypeK = return TypeK
> substKind m x (PiK bnd) = do
>   ((y, unembed -> a), k) <- unbind bnd
>   a' <- substType m x a
>   k' <- substKind m x k
>   return $ PiK $ bind (y, embed a') k'
>
> substType :: Fresh m => Term -> Var -> Type -> m Type
> substType m x (PT p) = do
>   p' <- substP m x p
>   return (PT p')
> substType m x (PiT bnd) = do
>   ((y, unembed -> a), b) <- unbind bnd
>   a' <- substType m x a
>   b' <- substType m x b
>   return $ PiT $ bind (y, embed a') b'
>
> substP :: Fresh m => Term -> Var -> P -> m P
> substP _ _ (AtmP a) = return (AtmP a)
> substP m x (AppP p n) = do
>   p' <- substP m x p
>   n' <- substTerm m x n
>   return (AppP p' n')

> substTerm :: Fresh m => Term -> Var -> Term -> m Term
> substTerm m x (RM r) = substR m x r
> substTerm m x (LamM bnd) = do
>   (y, n) <- unbind bnd
>   n' <- substTerm m x n
>   return $ LamM $ bind y n'

> substR :: Fresh m => Term -> Var -> R -> m Term
> substR m x r =
>   case headSpine x r of
>     Left rsp -> RM <$> substRRsp m x rsp
>     Right msp -> substMsp m x msp


> substRRsp :: Fresh m => Term -> Var -> Spine Head -> m R
> substRRsp _ _ (NilSp h) = return (headR h)
> substRRsp m x (AppSp sp n) = do
>   n' <- substTerm m x n
>   r <- substRRsp m x sp
>   return $ AppR r n'
>
> headR :: Head -> R
> headR (VarH y) = VarR y
> headR (ConstH c) = ConstR c

> substMsp :: Fresh m => Term -> Var -> Spine () -> m Term
> substMsp m _ (NilSp ()) = return m
> substMsp m x (AppSp s n) = do
>   o_ <- substMsp m x s
>   n' <- substTerm m x n
>   case o_ of
>     LamM bnd -> do
>       (y, o) <- unbind bnd
>       substTerm n' y o
>     _ -> error "can't happen"

Typechecking
============

> data Env = Env { _envAtm :: M.Map Atm Kind,
>                  _envConst :: M.Map Cnst Type,
>                  _envCtx :: M.Map Var Type }

> type Lens s t a b = forall f . Functor f => (a -> f b) -> s -> f t
> type Lens' s a = Lens s s a a

> type Setting s t a b = (a -> Identity b) -> s -> Identity t
> type Setting' s a = Setting s s a a

> over :: Setting s t a b -> (a -> b) -> s -> t
> over l f = runIdentity . l (Identity . f)

> set :: Setting s t a b -> b -> s -> t
> set l = over l . const

> type Getting r s a = (a -> Const r a) -> s -> Const r s

> views :: MonadReader s m => Getting a s a -> (a -> r) -> m r
> views l f = asks (\s -> f (getConst (l Const s)))

> envAtm :: Lens' Env (M.Map Atm Kind)
> envAtm afb s = fmap (\atms -> s { _envAtm = atms }) $ afb (_envAtm s)
>
> envCtx :: Lens' Env (M.Map Var Type)
> envCtx afb s = fmap (\ctx -> s { _envCtx = ctx } ) $ afb (_envCtx s)
>
> envConst :: Lens' Env (M.Map Cnst Type)
> envConst afb s = fmap (\sig -> s { _envConst = sig} ) $ afb (_envConst s)

> withSigOk :: (Fresh m, MonadReader Env m) => Signature -> m r -> m r
> withSigOk NilS kont = kont
> withSigOk (SnocAtom (unrebind -> (s, (a, unembed -> k)))) kont =
>   withSigOk s $ do
>   local (set envCtx M.empty) $ wfk k
>   local (over envAtm (M.insert a k)) kont
> withSigOk (SnocConst (unrebind -> (s, (c, unembed -> a)))) kont =
>   withSigOk s $ do
>   local (set envCtx M.empty) $ wfType a
>   local (over envConst (M.insert c a)) kont

> wfk :: (Fresh m, MonadReader Env m) => Kind -> m ()
> wfk TypeK = return ()
> wfk (PiK bnd) = do
>   ((x, unembed -> t), k) <- unbind bnd
>   wfType t
>   local (over envCtx (M.insert x t)) $ wfk k

> wfType :: (Fresh m, MonadReader Env m) => Type -> m ()
> wfType (PT p) = do
>   k <- inferP p
>   case k of
>     TypeK -> return ()
>     _ -> error "expected a type"
> wfType (PiT bnd) = do
>   ((x, unembed -> a), b) <- unbind bnd
>   wfType a
>   local (over envCtx (M.insert x a)) $ wfType b

> inferP :: (Fresh m, MonadReader Env m) => P -> m Kind
> inferP (AtmP atm) = lookupAtom atm
> inferP (AppP p m) = do
>   k <- inferP p
>   case k of
>     TypeK -> error "expected a pi kind"
>     PiK bnd -> do
>       ((x, unembed -> a), k') <- unbind bnd
>       checkTerm m a
>       substKind m x k'

> lookupOver :: MonadReader e m => Getting p e p -> String -> (p -> Maybe c) -> m c
> lookupOver l s f = do
>   mk <- views l f
>   case mk of
>     Nothing -> error $ "unbound " ++ s
>     Just c -> return c

> lookupAtom :: MonadReader Env m => Atm -> m Kind
> lookupAtom = lookupOver envAtm "atom" . M.lookup 

> lookupVar :: MonadReader Env m => Var -> m Type
> lookupVar = lookupOver envCtx "variable" . M.lookup

> lookupConst :: MonadReader Env m => Cnst -> m Type
> lookupConst = lookupOver envConst "constant" . M.lookup

> checkTerm :: (Fresh m, MonadReader Env m) => Term -> Type -> m ()
> checkTerm (LamM bnd) (PiT bnd') = do
>   mmatch <- unbind2 bnd bnd'
>   case mmatch of
>     Just (x, m, (_, unembed -> a), b) -> do
>       wfType a
>       local (over envCtx (M.insert x a)) $ checkTerm m b
>     Nothing -> error "did not match"
> checkTerm (RM r) (PT p) = do
>   t <- inferTerm r
>   case t of
>     (PT p') | p `aeq` p' -> return ()
>     _ -> error "atomic term doesn't have the expected atomic type."
> checkTerm (LamM {}) _ = error "lambda with no-PI type"
> checkTerm (RM {}) _ = error "atomic term with non-atomic type"

> inferTerm :: (Fresh m, MonadReader Env m) => R -> m Type
> inferTerm (VarR x) = lookupVar x
> inferTerm (ConstR c) = lookupConst c
> inferTerm (AppR r m) = do
>   p_ <- inferTerm r
>   case p_ of
>     PiT bnd -> do
>       ((x, unembed -> a), b) <- unbind bnd
>       checkTerm m a
>       substType m x b
>     PT {} -> error "expected a function in application position"



