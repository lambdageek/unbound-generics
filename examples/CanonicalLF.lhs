% Canonical LF using unbound-generics
% Aleksey Kliger
% June 2016

Canonical LF
============

This is a representation of [LF](http://www.twelf.org/) in which all terms are
automatically in *canonical form*.  The key idea is to segregate the type families
and the terms into *atomic* and *normal* forms where the term variables only stand
for atomic terms, and not arbitrary ones.  Then, a substitution procedure is defined
that takes terms in normal form and performs a substitution for a variable while
simultaneously normalizing any redices that occur.

> {-# LANGUAGE DeriveGeneric, StandaloneDeriving, DeriveDataTypeable,
>     ViewPatterns, RankNTypes, FlexibleContexts, FlexibleInstances,
>     FunctionalDependencies, TypeFamilies
>   #-}
> module CanonicalLF where
> import Unbound.Generics.LocallyNameless
> import GHC.Generics (Generic)
> import Data.Typeable (Typeable)
> import qualified Data.Map as M
> import Control.Monad.Reader
> import Control.Monad.Except
> import Data.Functor.Identity
> import Control.Applicative (Const(..))

Syntax
------

An LF signature introduces type family atoms and constant terms.

> data Signature = NilS
>   | SnocAtom (Rebind Signature (Atm, Embed Kind))
>   | SnocConst (Rebind Signature (Cnst, Embed Type))
>   deriving (Show, Generic, Typeable)

The type families are classified by kinds and may either be plain
types, or pi-kinds for families of types indexed by a term
variable.

> data Kind = TypeK | PiK (Bind (Var, Embed Type) Kind)
>   deriving (Show, Generic, Typeable)

The atomic type families are either type familiy atoms applied to zero
or more terms in normal form.

> type Atm = Name P
> data P = AtmP Atm | AppP P Term
>   deriving (Show, Generic, Typeable)

Type families in normal form are either atomic type families or dependent product
types indexed by a term variable of normal type.

> data Type = PT P | PiT (Bind (Var, Embed Type) Type)
>   deriving (Show, Generic, Typeable)

The atomic terms are either variables or constants applied to zero or
more terms in normal form.

> type Cnst = Name R
> type Var = Name R
> data R = VarR Var | ConstR Cnst | AppR R Term
>   deriving (Show, Generic, Typeable)

A term in normal form is either an atomic term or a lambda abstraction
that binds a term variable.

> data Term = RM R | LamM (Bind Var Term)
>   deriving (Show, Generic, Typeable)

When typechecking kinds, types or terms, new term variables may come
into scope. They are collected in contexts.

> data Context = NilC
>              | Snoc (Rebind Context (Var, Embed Type))
>              deriving (Show, Generic, Typeable)

All the syntactic objects are equivalent upto renaming of bound variables.

> instance Alpha Signature
> instance Alpha Kind
> instance Alpha P
> instance Alpha Type
> instance Alpha R
> instance Alpha Term
> instance Alpha Context

The metatheory of Canonical LF uses simple types to prove the
termination of hereditary substitution (defined below).  But they
aren't needed in the implementation.  (Although it would be
interesting to lift them to Haskell kinds and index the terms by the
simple types to disallow some malformed terms.)

> data SimpleType = AtmS Atm | ArrS SimpleType SimpleType
>   deriving (Show, Generic, Typeable)
>
> instance Alpha SimpleType

Hereditary Substitution
-----------------------

Variables in Canonical LF stand for atomic terms, but we will need to
subtitute terms for them.  If we used ordinary capture-avoiding
substitution, such substitution would produce redices, which we are
precisely what we don't want.  However redices will potentially only
occur when the variable for which we're substituting occurs at the
head of an atomic term.

> isHeadVarR :: Var -> R -> Bool
> isHeadVarR x (VarR y) = x == y
> isHeadVarR _ (ConstR _) = False
> isHeadVarR x (AppR r _) = isHeadVarR x r

Just using a boolean to decide if the variable is at the head of an
atomic term is fine, but we can actually partition an atomic term into
its head variable or constant together with a spine of applications.

> data Spine a = NilSp a | AppSp (Spine a) Term
> data Head = VarH Var | ConstH Cnst

If the variable for which we'll be substituting is at the head we only
really care about the spine.  Otherwise we have some other variable,
or perhaps a constant at the head.

> headSpine :: Var -> R -> Either (Spine Head) (Spine ())
> headSpine x (VarR y) | x == y    = Right (NilSp ())
>                      | otherwise = Left (NilSp (VarH y))
> headSpine _ (ConstR c)           = Left (NilSp (ConstH c))
> headSpine x (AppR r m)           = case headSpine x r of
>   Left s -> Left (AppSp s m)
>   Right s -> Right (AppSp s m)

Substitution in a kind just carries out substitution in the types.
Likewise substutition in normal type families.

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

Atomic type family application substitutes a term for a variable in the (normal) index terms.

> substP :: Fresh m => Term -> Var -> P -> m P
> substP _ _ (AtmP a) = return (AtmP a)
> substP m x (AppP p n) = do
>   p' <- substP m x p
>   n' <- substTerm m x n
>   return (AppP p' n')

Normal term substitution goes under a lambda (freshness is ensured by
the library) and into the atomic term.

> substTerm :: Fresh m => Term -> Var -> Term -> m Term
> substTerm m x (RM r) = substR m x r
> substTerm m x (LamM bnd) = do
>   (y, n) <- unbind bnd
>   n' <- substTerm m x n
>   return $ LamM $ bind y n'

To substitute in an atomic term we separate the head and the spine and
proceed according to whether the variable at the head is the one we
are substituting for.

> substR :: Fresh m => Term -> Var -> R -> m Term
> substR m x r =
>   case headSpine x r of
>     Left rsp -> RM <$> substRRsp m x rsp
>     Right msp -> substMsp m x msp

If there is another variable or a constant at the head, we will get
some kind of atomic term out since the head is unchanged and we only
substitute into the index terms.

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

When the variable we care about is at the head, we apply the
substitution to the rest of the spine to get a normal term (which, by
the metatheory will turn out to be some kind of a lambda), apply the
substitution to the index, and then carry out a new substitution of
the new index for the variable bound by the lambda to the body of the
lambda.  This last step is the heredetary part of heredetary
substitution.  The metatheory guarantees that this process will
terminate.  (Because the simple type of the body of the lambda is
smaller than the simple type of the original term).

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

We typecheck in an environment that maps type family atoms, term
costants and variables to their respective kinds and types.

> data Env = Env { _envAtm :: M.Map Atm Kind,
>                  _envConst :: M.Map Cnst Type,
>                  _envCtx :: M.Map Var Type }

> emptyEnv :: Env
> emptyEnv = Env M.empty M.empty M.empty

Some lenses to work with the environment

> envAtm :: Lens' Env (M.Map Atm Kind)
> envAtm afb s = fmap (\atms -> s { _envAtm = atms }) $ afb (_envAtm s)
>
> envCtx :: Lens' Env (M.Map Var Type)
> envCtx afb s = fmap (\ctx -> s { _envCtx = ctx } ) $ afb (_envCtx s)
>
> envConst :: Lens' Env (M.Map Cnst Type)
> envConst afb s = fmap (\sig -> s { _envConst = sig} ) $ afb (_envConst s)

And some combinators to perform lookups.

> lookupOver :: (MonadReader e m, MonadError String m) => Getting p e p -> String -> (p -> Maybe c) -> m c
> lookupOver l s f = do
>   mk <- views l f
>   case mk of
>     Nothing -> throwError $ "unbound " ++ s
>     Just c -> return c
>
> lookupAtom :: (MonadReader Env m, MonadError String m) => Atm -> m Kind
> lookupAtom = lookupOver envAtm "atom" . M.lookup 
>
> lookupVar :: (MonadReader Env m, MonadError String m) => Var -> m Type
> lookupVar = lookupOver envCtx "variable" . M.lookup
>
> lookupConst :: (MonadReader Env m, MonadError String m) => Cnst -> m Type
> lookupConst = lookupOver envConst "constant" . M.lookup

To check a signature we check the kind or type classifying the atom or
constant and then continue in an environment extended with the new
binding.

> withSigOk :: (Fresh m, MonadReader Env m, MonadError String m) => Signature -> m r -> m r
> withSigOk NilS kont = kont
> withSigOk (SnocAtom (unrebind -> (s, (a, unembed -> k)))) kont =
>   withSigOk s $ do
>   local (set envCtx M.empty) $ wfk k
>   local (over envAtm (M.insert a k)) kont
> withSigOk (SnocConst (unrebind -> (s, (c, unembed -> a)))) kont =
>   withSigOk s $ do
>   local (set envCtx M.empty) $ wfType a
>   local (over envConst (M.insert c a)) kont

Kind and normal type formation is unsurprising.  Note that PT is only
well-formed when the atomic type family is fully applied and is of
base kind.

> wfk :: (Fresh m, MonadReader Env m, MonadError String m) => Kind -> m ()
> wfk TypeK = return ()
> wfk (PiK bnd) = do
>   ((x, unembed -> t), k) <- unbind bnd
>   wfType t
>   local (over envCtx (M.insert x t)) $ wfk k
>
> wfType :: (Fresh m, MonadReader Env m, MonadError String m) => Type -> m ()
> wfType (PT p) = do
>   k <- inferP p
>   case k of
>     TypeK -> return ()
>     _ -> throwError "expected a type"
> wfType (PiT bnd) = do
>   ((x, unembed -> a), b) <- unbind bnd
>   wfType a
>   local (over envCtx (M.insert x a)) $ wfType b

For atomic type families we infer their kinds.  For atoms we read the
kind off from the environment.  For applications we infer the kind of
the type family (which had better be a pi kind), and then check that
the term argument has the expected type and then return the resulting
kind where we (heredeterily) substitute the term for the index
variable.

> inferP :: (Fresh m, MonadReader Env m, MonadError String m) => P -> m Kind
> inferP (AtmP atm) = lookupAtom atm
> inferP (AppP p m) = do
>   k <- inferP p
>   case k of
>     TypeK -> throwError "expected a pi kind"
>     PiK bnd -> do
>       ((x, unembed -> a), k') <- unbind bnd
>       checkTerm m a
>       substKind m x k'

To check that a term in normal form has the expected normal type, we
check that its either a lambda of pi type, or an atomic term of atomic
type.  The latter ensures that terms are in eta long form by requiring
all variables and constants to be fully applied.

We infer the type of an atomic term (which had better be atomic) and
then check that it is alpha-equivalent to the given atomic type.
Because the calculus is constructed to only allow terms in normal
form, alpha equivalence suffices and we don't have to do any
normalization.  (We paid that price in heredetary substitution.)

> checkTerm :: (Fresh m, MonadReader Env m, MonadError String m) => Term -> Type -> m ()
> checkTerm (LamM bnd) (PiT bnd') = do
>   mmatch <- unbind2 bnd bnd'
>   case mmatch of
>     Just (x, m, (_, unembed -> a), b) -> do
>       wfType a
>       local (over envCtx (M.insert x a)) $ checkTerm m b
>     Nothing -> throwError "did not match"
> checkTerm (RM r) (PT p) = do
>   t <- inferTerm r
>   case t of
>     (PT p') | p `aeq` p' -> return ()
>     _ -> throwError "atomic term doesn't have the expected atomic type."
> checkTerm (LamM {}) _ = throwError "lambda with no-PI type"
> checkTerm (RM {}) _ = throwError "atomic term with non-atomic type"

To infer the type of a term, we lookup variables and constants in the
environment.  For applications we ensure that the head has some kind
of pi type and then check the index against the argument type, and
then return the result type with the argument substituted for the
index variable.

> inferTerm :: (Fresh m, MonadReader Env m, MonadError String m) => R -> m Type
> inferTerm (VarR x) = lookupVar x
> inferTerm (ConstR c) = lookupConst c
> inferTerm (AppR r m) = do
>   p_ <- inferTerm r
>   case p_ of
>     PiT bnd -> do
>       ((x, unembed -> a), b) <- unbind bnd
>       checkTerm m a
>       substType m x b
>     PT {} -> throwError "expected a function in application position"

Smart Constructors
==================

This section defines a little DSL for writing Canonical LF terms in
Haskell.  It's a higher-order encoding that uses haskell variable
binding to represent LF binding constructs.

We use a higher-kinded repr parameter to allow for different sorts of
interpretations for this DSL.  Although in this example we only build
one using the Syn newtype to wrap a fresh-name monad computation that
just builds a term in our original AST, above.

> class TermSyntax repr r n | r -> n, n -> r where
>   lam :: String -> ((repr r) -> (repr n)) -> (repr n)
>   app :: repr r -> repr n -> repr r
>   rm :: repr r -> repr n
>
> newtype Syn m a = Syn { unSyn :: m a } 
>
> instance Fresh m => TermSyntax (Syn m) R Term where
>   lam hint f = Syn $ do
>     x <- fresh (s2n hint)
>     m <- unSyn $ f (Syn $ return $ VarR x)
>     return $ LamM (bind x m)
>   app r n = Syn (AppR <$> unSyn r <*> unSyn n)
>   rm r = Syn (RM <$> unSyn r)

> class  TypeSyntax repr p a | a -> p, p -> a where
>   type TermInType repr a :: *
>   type RInType repr a :: *
>   piT :: String -> repr a -> (repr (RInType repr a) -> repr a) -> repr a
>   arrT :: repr a -> repr a -> repr a
>   arrT a b = piT "_" a (const b)
>   appP :: repr p -> repr (TermInType repr a) -> repr p
>   pt :: repr p -> repr a

> instance Fresh m => TypeSyntax (Syn m) P Type where
>   type TermInType (Syn m) Type = Term
>   type RInType (Syn m) Type = R
>   piT hint sa f = Syn $ do
>     x <- fresh (s2n hint)
>     b <- unSyn $ f (Syn $ return $ VarR x)
>     a <- unSyn sa
>     return $ PiT $ bind (x, embed a) b
>   appP p m = Syn (AppP <$> unSyn p <*> unSyn m)
>   pt p = Syn (PT <$> unSyn p)

> class KindSyntax repr k where
>   type TypeInKind repr k :: *
>   type RInKind repr k :: *
>   typeK :: repr k
>   piK :: String -> repr (TypeInKind repr k) -> (repr (RInKind repr k) -> repr k) -> repr k
>   arrK :: repr (TypeInKind repr k) -> repr k -> repr k
>   arrK a k = piK "_" a (const k)

> instance Fresh m => KindSyntax (Syn m) Kind where
>   type TypeInKind (Syn m) Kind = Type
>   type RInKind (Syn m) Kind = R
>   typeK = Syn $ return TypeK
>   piK hint sa sk = Syn $ do
>     x <- fresh (s2n hint)
>     a <- unSyn sa
>     k <- unSyn $ sk (Syn $ return $ VarR x)
>     return $ PiK $ bind (x, embed a) k

> class SignatureSyntax repr sig p r | sig -> p r where
>   type KindInSig repr sig :: *
>   type TypeInSig repr sig :: *
>   letAtom :: String -> repr (KindInSig repr sig) -> (repr p -> repr sig) -> repr sig
>   letConstant :: String -> repr (TypeInSig repr sig) -> (repr r -> repr sig) -> repr sig
>   endSig :: repr sig
>
> instance Fresh m => SignatureSyntax (Syn m) (Signature -> Signature) P R where
>   type KindInSig (Syn m) (Signature -> Signature) = Kind
>   type TypeInSig (Syn m) (Signature -> Signature) = Type
>
>   letAtom hint sk kont = Syn $ do
>     a <- fresh (s2n hint)
>     k <- unSyn sk
>     f <- unSyn $ kont $ Syn $ return $ AtmP a
>     return $ \sig -> f (SnocAtom $ rebind sig (a, embed k))
>
>   letConstant hinst st kont = Syn $ do
>     c <- fresh (s2n hinst)
>     t <- unSyn st
>     f <- unSyn $ kont $ Syn $ return $ ConstR c
>     return $ \sig -> f (SnocConst $ rebind sig (c, embed t))
>
>   endSig = Syn $ return id

> infixr 6 `arrT`, `arrK`
> infixl 6 `appP`, `app`

Example
-------

An LF signature fragment for first-order logic.

> example1 :: Fresh m => Syn m (Signature -> Signature)
> example1 =
>   letAtom "o" typeK $ \o ->
>   letConstant "tt" (pt o) $ \tt ->
>   letConstant "ff" (pt o) $ \ff ->
>   letConstant "not" (pt o `arrT` pt o) $ \not ->
>   letConstant "and" (pt o `arrT` pt o `arrT` pt o) $ \and ->
>   letAtom "nd" (pt o `arrK` typeK) $ \nd ->
>   letConstant "tti" (pt (nd `appP` rm tt)) $ \tti ->
>   letConstant "ffe" (piT "a" (pt o) $ \a ->
>                        pt (nd `appP` rm ff)
>                        `arrT`
>                        pt (nd `appP` rm a)) $ \ffe ->
>   letConstant "noti" (piT "a" (pt o) $ \a ->
>                          (piT "p" (pt o) $ \p ->
>                              pt (nd `appP` rm a)
>                              `arrT`
>                              pt (nd `appP` rm p))
>                          `arrT`
>                          pt (nd `appP` rm (not `app` rm a))) $ \noti ->
>   letConstant "note" (piT "a" (pt o) $ \a -> piT "c" (pt o) $ \c ->
>                          pt (nd `appP` rm (not `app` rm a))
>                          `arrT`
>                          pt (nd `appP` rm a)
>                          `arrT`
>                          pt (nd `appP` rm c)) $ \note ->
>   letConstant "andi" (piT "a" (pt o) $ \a -> piT "b" (pt o) $ \b ->
>                          pt (nd `appP` rm a)
>                          `arrT`
>                          pt (nd `appP` rm b)
>                          `arrT`
>                          pt (nd `appP` rm (and `app` rm a `app` rm b))) $ \andi ->
>   letConstant "ande1" (piT "a" (pt o) $ \a -> piT "b" (pt o) $ \b ->
>                           pt (nd `appP` rm (and `app` rm a `app` rm b))
>                           `arrT`
>                           pt (nd `appP` rm a)) $ \ande1 ->
>   letConstant "ande2" (piT "a" (pt o) $ \a -> piT "b" (pt o) $ \b ->
>                           pt (nd `appP` rm (and `app` rm a `app` rm b))
>                           `arrT`
>                           pt (nd `appP` rm b)) $ \ande2 ->
>   endSig

> checkSynSig :: (Fresh m, MonadReader Env m, MonadError String m) => Syn m (Signature -> Signature) -> m ()
> checkSynSig sig = do
>   sigf <- unSyn sig
>   withSigOk (sigf NilS) $ return ()

Example:
```haskell
  >>> runExceptT $ runFreshMT $ runReaderT (checkSynSig example1) emptyEnv
  Right ()
```

Appendix: Lens utilities
==============

Some machinery to work with records.

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

