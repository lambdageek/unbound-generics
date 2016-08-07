% "Meta-programming with names and necessity" using unbound-generics
% Aleksey Kliger
% August 2016


Introduction
============

This example is based on Nanevski's “Meta-programming with Names and
Necessity”[1](http://reports-archive.adm.cs.cmu.edu/anon/2002/CMU-CS-02-123R.pdf).
In particular, it demonstrates how to represent a language with
multiple sorts of names (value variables, code variables, nominals and
support variables) some with non-standard notions of substitution.

As a tutorial example, we show how to represent the language and
demonstrate its operational semantics.  Additionally, this document
includes a typecheker and pretty printer.

This file is Literate Haskell, so we start with some boilerplate.

Every `unbound-generics` syntax representation needs `deriving (Show, Generic, Typeable)` declarations for all the datatypes.

> {-# language DeriveDataTypeable, DeriveGeneric #-}

> {-# language MultiParamTypeClasses,
>     FlexibleContexts, FlexibleInstances, DefaultSignatures, ViewPatterns, RankNTypes,
>     GeneralizedNewtypeDeriving #-}
> module Nanevski where
> import GHC.Generics (Generic)
> import Data.Typeable (Typeable)
> import Unbound.Generics.LocallyNameless
> import Unbound.Generics.LocallyNameless.Internal.Fold (Fold, foldMapOf)
> import qualified Unbound.Generics.PermM as PermM
>
> import Control.Monad.Except
> import Control.Monad.State
> import Control.Monad.Writer
> import Control.Monad.Reader
> import Data.List (partition, nub, sort, (\\), isSubsequenceOf)
> import Data.Monoid (Any (..))
> import Data.Either (partitionEithers)
> import qualified System.IO as IO
> import qualified Text.PrettyPrint.ANSI.Leijen as PP
> import Text.PrettyPrint.ANSI.Leijen ()

Introduction to meta-programming
--------------------------------

Meta-programming is the process of writing programs that create,
manipulate or reason about other programs.  The meta-program is
written in the *meta-language* and it manipulates *object-language*
programs.

In the system in this document, the object language and the
meta-language coincide.  In general they could be different (for
example the meta-language could be compiled down to machine code,
while the object-language remains as some sort of abstract syntax
trees).

The type discipline of the system in this document applies both to the
meta- and object-languages: a well-typed meta-program can only
construct well-typed object-language programs.

One important concept is the *support* of an object-language
expression: it is the set of meta-language names that appear within
the object-language program fragment.  The meta-language program may
compose larger object-language fragments by substituting
object-language expressions for the names.

Example
-------

Suppose we wanted to construct the object-language cube function `“λx:int. 1 * x * x * x”`

The following program constructs such a function:

> -- >>> ppretty (pexp @@ number 3)
> -- (λn:int.
> --  choose
> --  (νX∼int.
> --   let □w = (Λp.
> --             λe:□_{p} int.
> --             rec
> --               go (m:int) : □_{p} int
> --               is if (□_{p} int;
> --                      m ≤ 0;
> --                      λ_:(). “1”;
> --                      λ_:(). let □u = go (m + -1) in let □w = e in “⟨⟩u * ⟨⟩w”)
> --                  ()) {X}
> --            “X”
> --            n in “λx:int. ⟨X ↦ x⟩w”))
> -- 3


Syntax
======

Types
-----


> data BaseType = UnitT | BoolT | IntT
>   deriving (Typeable, Generic, Show)

> data Support = Support { supportNominals :: ![Nominal],
>                          supportVars :: ![SupportVar] }
>   deriving (Typeable, Generic, Show)
> type SupportVar = Name Support

> data Type =
>   BaseT BaseType          -- some base types
>   | ArrT Type Type        -- τ₁→τ₂ functions
>   | BoxT Type Support   -- □_C τ is the type of code of type τ with support C
>   | NomArrT Type Type      -- τ₁ ↛ τ₂ is the type of νN:τ₁.e brings a
>                           -- new name N associated with type τ₁ into
>                           -- scope in a body of type τ₂.  The new
>                           -- name cannot appear in the type τ₂ or in
>                           -- the support of e.  It is thus
>                           -- guaranteed to either be substituted
>                           -- away or only appear in code in e, not
>                           -- in subexpresisons that may be evaluated
>                           -- in teh course of evaluating e.
>   | ForallSupT (Bind SupportVar Type) -- support-polymorphic functions
>   deriving (Typeable, Generic, Show)

Meta-language expressions
-------------------------

> data Expr =
>   V Var
>   | U NominalSubst CodeVar
>   | N Nominal
>   | C BaseConst
>   | P PrimOp [Value] [Expr] -- partially evaluated primop p v₁...vₙ e₁...eₘ
>   | Lambda (Bind (Var, Embed Type) Expr)
>   | RecFun (Bind (Var, Var, Embed Type, Embed Type) Expr) -- fun f (x : τ₁) : τ₂ = e
>   | App Expr Expr
>   | Let Expr (Bind Var Expr)
>   | Box Code  -- A box expression represents some syntactic code as a data structure.
>   | LetBox Expr (Bind CodeVar Expr)
>   | New (Bind (Nominal, Embed Type) Expr)   -- the New operation brings names into scope; it is the job of the type system to ensure that the new name does not appear in the type of the body, nor its support.
>   | Choose Expr
>   | PLamSupport (Bind SupportVar Expr)
>   | PAppSupport Expr Support
>   deriving (Typeable, Generic, Show)
>
> data BaseConst = UnitC | BoolC !Bool | IntC !Int
>   deriving (Typeable, Generic, Show)
> data PrimOp = IfPrim Type | AddPrim | MulPrim | LeqPrim
>   deriving (Typeable, Generic, Show)

>
> type Var = Name Expr

Ordinary variables just stand for expressions.

> type Value = Expr


> isValue :: Expr -> Bool
> isValue (C _) = True
> isValue (Lambda _) = True
> isValue (Box _) = True
> isValue (New _) = True
> isValue (PLamSupport _) = True
> isValue _ = False

Object-level Code
-----------------

Think of Code as some data structure that the expressions can build
up.  Code is a first-class value in this language.  You can build it
up, pass it to functions, return it as a result etc.  Code that is
open has non-empty support is guaranteed by the type system not to be
evaluated.  Code that is closed and has empty support , on the other
hand may appear in expressions in positions where it may potentially
be run.

> newtype Code = Code { codeExpr :: Expr }
>   deriving (Typeable, Generic, Show)
> type CodeVar = Name Code

Code variables stand for code, but they only occur in expressions
together with an explicit subtitution that substitutes away some Nominals.

> newtype NominalSubst = NominalSubst { nominalSubst :: [(Nominal, Nom)] }
>   deriving (Typeable, Generic, Show)

Nominals
--------

A Nominal can appear in code (but not in an expression that may be
evaluated).  It stands for an expression just like Var, but in
unbound-generics since we want to treat Nominal and Var distinctly, we
add a newtype wrapper around Expr and call it a Nom.

> newtype Nom = Nom {nomExpr :: Expr }
>   deriving (Typeable, Generic, Show)
> type Nominal = Name Nom

Alpha renaming, free names, alpha-equivalence boilerplate
---------------------------------------------------------

All the types we defined will participate in various Alpha operations:
we can collect the free Variabes, Nominals or CodeVars of all the
syntactic categories.  They are also subject to alpha equivalence upto
renaming of bound occurrances, etc.

> instance Alpha Nom
> instance Alpha Code
> instance Alpha Support
> instance Alpha NominalSubst
> instance Alpha Type
> instance Alpha Expr
> instance Alpha BaseType
> instance Alpha BaseConst
> instance Alpha PrimOp

Substitution
============

We also have notions of substitution for variables, nominals and code variables.

For base types, constants and primitive operations, we give some
catch-all substitution operations since they cannot contain any sort
of name.

> instance Subst a BaseType where
>   subst _ _ = id
>   substs _ = id
>
> instance Subst a BaseConst where
>   subst _ _ = id
>   substs _ = id
>
> instance Subst Expr PrimOp where
>   subst _ _ = id
>   substs _ = id
> instance Subst Code PrimOp where
>   subst _ _ = id
>   substs _ = id
> instance Subst Nom PrimOp
> instance Subst Support PrimOp

Expression substitution
-----------------------

Ordinary variables can occur in expressions as well as code, noms and
nominal substitutions.  They don't occur in types, so we can
short-circuit substitution there and return the type unchanged.

> instance Subst Expr Type where
>   subst _ _ = id
>   substs _ = id
> instance Subst Expr Expr where
>   isvar (V v) = Just (SubstName v)
>   isvar _ = Nothing
> instance Subst Expr NominalSubst
> instance Subst Expr Nom
> instance Subst Expr Support where
>   subst _ _ = id
>   substs _ = id

Nominal substitution
--------------------

> instance Subst Nom Nom
> instance Subst Nom Support

To substitute for a nominal N in an expression e, we use need to use
\texttt{isCoerceVar} to pull out the expression from the Nom being
substituted.

> instance Subst Nom Expr where
>   isCoerceVar (N n) = Just $ SubstCoerce n (Just . nomExpr)
>   isCoerceVar _ = Nothing

An important property (justified by the type system) of this language
is that when substituting for a name N or ordinary variable v in an
expression Box (Code e) we can just return Box (Code e) unchanged
since the type system prevents Code from depending on the ordinary
variable context or by using names that do not contribute to the
support of a term.

> instance Subst Nom Code where
>   subst _ _ = id
>   substs _ = id
> instance Subst Expr Code where
>   subst _ _ = id
>   substs _ = id

> instance Subst Nom Type
> instance Subst Nom NominalSubst

Code substitution
-----------------

> instance Subst Code Code

We can substitute for code variables u in expressions, but since
u's appear only together with an explicit substitution for its
Nominals, we use \texttt{isCoerceVar} to have unbound-generics perform
the nominal substitution.

> instance Subst Code Expr where
>   isCoerceVar (U noms u) = Just $ SubstCoerce u (Just . substituteSupported noms)
>   isCoerceVar _ = Nothing
>

Note that in this case we peek inside a \texttt{(Code e)} using
codeExpr. (Just using \texttt{substs (nominalSubst noms) c} would give
us back the same unchanged syntactic object!)

> substituteSupported :: NominalSubst -> Code -> Expr
> substituteSupported noms c = substs (nominalSubst noms) (codeExpr c)

> instance Subst Code NominalSubst
> instance Subst Code Nom

> instance Subst Code Type where
>   subst _ _ = id
>   substs _ = id

> instance Subst Code Support where
>   subst _ _ = id
>   substs _ = id

Support polymorphism substitution
---------------------------------

Support variables stand for support sets.  We have to do a bit of
juggling to normalize the result of the substitution.

> instance Subst Support Support where
>   subst v sup sup0@(Support noms vs) =
>     case Data.List.partition (== v) vs of
>       ((_:_), vs') -> let
>         noms' = sort (supportNominals sup ++ noms)
>         vs'' = sort (supportVars sup ++ vs')
>         in Support noms' vs''
>       _ -> sup0
>   substs ss (Support noms vs) =
>     let f v = case lookup v ss of
>           Just sup -> Left sup
>           Nothing -> Right v
>         (sups, vs') = partitionEithers (map f vs)
>         noms' = sort (concatMap supportNominals sups ++ noms)
>         vs'' = sort (concatMap supportVars sups ++ vs')
>         in Support noms' vs''

> instance Subst Support Type

> instance Subst Support Expr
> instance Subst Support Nom
> instance Subst Support NominalSubst

As with Nominals, since SupportVars stand for the support of an
expression, and boxed code is meant to have empty support until it is
unboxed and evaluated, the support variable substitution on code is
the identity.

> instance Subst Support Code where
>   subst _ _ = id
>   substs _ = id

Operational Semantics
=====================

The operational semantics take configurations consisting of a context
of Nominals together with their associated types and an expression
with empty support to another such configuration.

> data NomCtx = NilNC | SnocNC (Rebind NomCtx (Nominal, Embed Type))
>             | SnocSupNC (NomCtx, SupportVar)
>   deriving (Typeable, Generic, Show)
> instance Alpha NomCtx

A configuration just pairs together a nominal ctx and an expression in some manner.
We will use a state monad. But we could also bind the names of the context in the expression.

> type ClosedConfig = Bind NomCtx Expr

We will need to work in a monad that also gives us fresh names and a way to signal errors

> step :: (MonadError String m, MonadState NomCtx m, Fresh m) => Expr -> m Expr
> step e0 = case e0 of
>   V v -> evalError ("unbound variable: "  ++ show v)
>   U _ u -> evalError ("unbound code variable: " ++ show u)
>   N n -> evalError ("unbound name: " ++ show n)
>   C c -> evalError ("already a value: " ++ show c)
>   P p vs [] -> applyPrim p vs
>   P p vs (e:es) | isValue e -> pure (P p (vs ++ [e]) es) 
>                 | otherwise -> P p vs <$> ((:) <$> step e <*> pure es)
>   Lambda _ -> evalError ("already a value: " ++ show e0)
>   efun@(RecFun bnd) -> do
>     ((f, x, t1, _), e) <- unbind bnd
>     return $ Lambda $ bind (x, t1) (subst f efun e)
>   Let e1 bnd | isValue e1 -> do
>                  (x, e2) <- unbind bnd
>                  return $ subst x e1 e2
>   Let e1 bnd -> Let <$> step e1 <*> pure bnd
>   Box _ -> evalError ("already a value: " ++ show e0)
>   App e1@(Lambda bnd) e2 | isValue e2 -> do
>                              ((x, _), ebody) <- unbind bnd
>                              return $ subst x e2 ebody
>                          | otherwise -> do
>                              App e1 <$> step e2
>   App e1 e2 -> App <$> step e1 <*> pure e2
>   LetBox (Box c) bnd -> do
>     (u, ebody) <- unbind bnd
>     return $ subst u c ebody
>   LetBox e1 bnd -> LetBox <$> step e1 <*> pure bnd
>   New _ -> evalError ("already a value: " ++ show e0)
>   Choose (New bnd) -> do
>     -- In the paper there's a side-condition here that the chosen
>     -- name has to be fresh (with respect to the nominal ctx.
>     -- Fortunately unbound-generics will always give us a fresh
>     -- name.
>     (nt, ebody) <- unbind bnd
>     modify (\ctx -> SnocNC $ rebind ctx nt)
>     return ebody
>   Choose e -> Choose <$> step e
>   PLamSupport _ -> evalError ("already a value: " ++ show e0)
>   PAppSupport (PLamSupport bnd) sup -> do
>     (sv, ebody) <- unbind bnd
>     return $ subst sv sup ebody
>   PAppSupport e1 sup -> PAppSupport <$> step e1 <*> pure sup

> evalError :: MonadError String m => String -> m a
> evalError = throwError

> applyPrim :: MonadError String m => PrimOp -> [Value] -> m Value
> applyPrim (IfPrim _t) [C (BoolC b), v1, v2] = return $ if b then v1 else v2
> applyPrim AddPrim [C (IntC x), C (IntC y)] = return $ C $ IntC $ x + y
> applyPrim MulPrim [C (IntC x), C (IntC y)] = return $ C $ IntC $ x * y
> applyPrim LeqPrim [C (IntC x), C (IntC y)] = return $ C $ BoolC $ x <= y
> applyPrim p vs = evalError (show p ++ show vs ++ " does not step")

> eval :: (Fresh m, MonadState NomCtx m, MonadError String m) => Expr -> m Expr
> eval e = if isValue e then return e else step e >>= eval
  
Evaluation Example
==================

A little DSL for term construction
----------------------------------

> lam :: String -> Type -> (Expr -> Expr) -> Expr
> lam s t f =
>   let x = s2n s
>   in Lambda $ bind (x, embed t) (f $ V x)

> recFun :: String -> String -> Type -> Type -> (Expr -> Expr -> Expr) -> Expr
> recFun sfn sx t1 t2 f =
>   let fn = s2n sfn
>       x = s2n sx
>   in RecFun $ bind (fn, x, embed t1, embed t2) (f (V fn) (V x))

> plam :: String -> (SupportVar -> Expr) -> Expr
> plam s f =
>   let sv = s2n s
>   in PLamSupport (bind sv (f sv))

> intT, unitT, boolT :: Type
> intT = BaseT IntT
> unitT = BaseT UnitT
> boolT = BaseT BoolT
> boxT :: Type -> [Nominal] -> [SupportVar] -> Type
> boxT t noms svs = BoxT t (Support noms svs)
> boxT_ :: Type -> [Nominal] -> Type
> boxT_ t noms = boxT t noms []
> arrT :: Type -> Type -> Type
> arrT = ArrT
> infixr 5 `arrT`
> forallSupT :: String -> (SupportVar -> Type) -> Type
> forallSupT s f =
>   let sv = s2n s
>   in ForallSupT (bind sv (f sv))

> (@@) :: Expr -> Expr -> Expr
> (@@) = App
> infixl 5 @@

> papp :: Expr -> [Nominal] -> [SupportVar] -> Expr
> papp e noms svs = PAppSupport e (Support noms svs)

> chooseNew :: String -> Type -> (Nominal -> Expr) -> Expr
> chooseNew s t f =
>   let n = s2n s
>   in Choose $ New $ bind (n, embed t) (f n)

> letExp :: String -> Expr -> (Expr -> Expr) -> Expr
> letExp s e1 f =
>   let x = s2n s
>   in Let e1 (bind x (f $ V x))

> letBox :: String -> Expr -> (CodeVar -> Expr) -> Expr
> letBox s e1 f =
>   let u = s2n s
>   in LetBox e1 (bind u (f u))

> box :: Expr -> Expr
> box = Box . Code

> code :: [(Nominal, Expr)] -> CodeVar -> Expr
> code nome = U (NominalSubst $ map (fmap Nom) nome)

> runCode :: CodeVar -> Expr
> runCode = U (NominalSubst []) 

> name :: Nominal -> Expr
> name = N

> number :: Int -> Expr
> number = C . IntC 

> ifLeqZ :: Type -> Expr -> Expr -> Expr -> Expr
> ifLeqZ tres ex etrue efalse =
>   App (P (IfPrim tres) [] [etest, thunk etrue, thunk efalse]) (C UnitC)
>   where
>     etest = P LeqPrim [] [ex, number 0]
>     thunk e = lam "_" unitT (\_ -> e)

> sub1 :: Expr -> Expr
> sub1 e = P AddPrim [] [e, number (-1)]

> add, mul :: Expr -> Expr -> Expr
> add e1 e2 = P AddPrim [] [e1, e2]
> mul e1 e2 = P MulPrim [] [e1, e2]

> infixl 6 `add`
> infixl 7 `mul`

> (~~) :: a -> b -> (a, b)
> (~~) = (,)
> infix 5 ~~

Example: Staged exponential function
------------------------------------

(Note that within the calculus itself there's not a way to abstract over a nominal like this - the example below chooses a new X which appears in the definition of this helper function.)

First a little recursive helper function that expands out to the m-fold multiplication code \texttt{X * X * X * ... * 1}

> exp' :: Nominal -> Expr
> exp' nX = recFun "exp'" "m" intT (boxT_ intT [nX]) $ \exp' m ->
>   ifLeqZ intT m (box $ number 1) (letBox "u" (exp' @@ (sub1 m)) $ \u ->
>                                      box $ mul (name nX) (runCode u))
>   

And the example exponential function takes an integer n and then constructs a piece of code consiting of a lambda abstraction whose argument x is multiplied with itself n times.

> expon :: Expr
> expon = lam "n" intT $ \n ->
>   chooseNew "X" intT $ \nX ->
>   letExp "exp'" (exp' nX) $ \exp' ->
>   letBox "v"  (exp' @@ n) $ \v ->
>   box (lam "x" intT $ \x -> code [nX ~~ x] v)

Let's set up an environment for running evaluations.

> run :: StateT NomCtx (ExceptT String FreshM) a -> Either String (a, NomCtx)
> run comp = runFreshM (runExceptT (runStateT comp NilNC))

Running the example \texttt{expon 3} we get the expected final
configuration of \texttt{box (λx : int . x * x * x * 1)} and the used
name X1 (which doesn't appear in the code, and therefore we could run
the code).

> -- >>> run (eval (expon @@ number 3))
> -- Right (Box (Code {codeExpr = Lambda (<(x,{BaseT IntT})> P MulPrim [] [V 0@0,P MulPrim [] [V 0@0,P MulPrim [] [V 0@0,C (IntC 1)]]])}),SnocNC (<<NilNC>> (X1,{BaseT IntT})))

> -- >>> run (eval (letBox "exp3" (expon @@ number 3) $ \exp3 -> (runCode exp3) @@ number 2))
> -- Right (C (IntC 8),SnocNC (<<NilNC>> (X1,{BaseT IntT})))


Example: Staged support-polymorphic exponential kernel
------------------------------------------------------

> pexpKernel :: Expr
> pexpKernel = plam "p" $ \sp ->
>   let tResult = boxT intT [] [sp]
>   in lam "e" tResult $ \e ->
>     recFun "go" "m" intT tResult $ \go m ->
>     ifLeqZ tResult m (box $ number 1) (letBox "u" (go @@ (sub1 m)) $ \u ->
>                                           letBox "w" e $ \w ->
>                                           box $ mul (runCode u) (runCode w))

> -- >>> run $ eval (papp pexpKernel [] [] @@ box (number 42) @@ number 3)
> -- Right (Box (Code {codeExpr = P MulPrim [] [P MulPrim [] [P MulPrim [] [C (IntC 1),C (IntC 42)],C (IntC 42)],C (IntC 42)]}),NilNC)

> pexp :: Expr
> pexp = lam "n" intT $ \n ->
>   chooseNew "X" intT $ \nX ->
>   letBox "w" (papp pexpKernel [nX] [] @@ box (name nX) @@ n) $ \w ->
>   box (lam "x" intT $ \x -> code [nX ~~ x] w)

> -- >>> run $ eval (pexp @@ number 5)
> -- Right (Box (Code {codeExpr = Lambda (<(x,{BaseT IntT})> P MulPrim [] [P MulPrim [] [P MulPrim [] [P MulPrim [] [P MulPrim [] [C (IntC 1),V 0@0],V 0@0],V 0@0],V 0@0],V 0@0])}),SnocNC (<<NilNC>> (X1,{BaseT IntT})))

> -- >>> run $ eval (letBox "c" (pexp @@ number 5) $ \c -> runCode c @@ number 2)
> -- Right (C (IntC 32),SnocNC (<<NilNC>> (X1,{BaseT IntT})))


Appendix: Type checking and support inference
=============================================

> class Fresh m => TC m where
>  lookupSupportVar :: SupportVar -> m () -- just check it exists
>  lookupVar :: Var -> m Type
>  lookupCodeVar :: CodeVar -> m (Type, Support)
>  lookupNom :: Nominal -> m Type
>  extendVar :: Var -> Type -> m a -> m a
>  extendCodeVar :: CodeVar -> Type -> Support -> m a -> m a
>  extendNom :: Nominal -> Type -> m a -> m a
>  extendSupportVar :: SupportVar -> m a -> m a
>
>  tcError :: String -> m a
>  default tcError :: (MonadError String m) => String -> m a
>  tcError = throwError
>
>  inSupport :: Nominal -> m ()
>  inSupport n = includeSupport (Support [n] [])
>  includeSupport :: Support -> m ()
>  default includeSupport :: (MonadWriter Support m) => Support -> m ()
>  includeSupport = tell
>
>  -- run the subcomputation, grab its support and then completely censor it
>  withEmptySupport :: m a -> m (a, Support)
>  default withEmptySupport :: (MonadWriter Support m) => m a -> m (a, Support)
>  withEmptySupport comp =
>    let censorEverything = const mempty
>    in pass ((\asup -> (asup, censorEverything)) <$> listen comp)
>    

> wellFormed :: TC m => Type -> m ()
> wellFormed t0 =
>   case t0 of
>     BaseT {} -> return ()
>     (ArrT t1 t2) -> wellFormed t1 >> wellFormed t2
>     (NomArrT t1 t2) -> wellFormed t1 >> wellFormed t2
>     (BoxT t sup) -> wellFormed t >> wellFormedSupport sup
>     (ForallSupT bnd) -> do
>       (sv, t) <- unbind bnd
>       extendSupportVar sv $ wellFormed t
>     _ -> tcError ("Unimplemented! " ++ show t0)

> wellFormedSupport :: TC m => Support -> m ()
> wellFormedSupport (Support _noms svs) = mapM_ lookupSupportVar svs

> newtype Expected a = Expecting { unExpecting :: a }

> inferExpr :: TC m => Expr -> m Type
> inferExpr e = inferExpr_ e (Expecting Nothing)

> expecting :: TC m => Expected (Maybe Type) -> Type -> m Type
> expecting (Expecting Nothing) t = return t
> expecting (Expecting (Just texp)) t = do
>   unless (t `aeq` texp) $ tcError $ "expected type " ++ show texp ++ " but got " ++ show t
>   return texp

> expectingSup :: TC m => Expected (Maybe Support) -> Support -> m Support
> expectingSup (Expecting Nothing) sup = return sup
> expectingSup (Expecting (Just supexp)) sup = do
>   unless (sup `subsup` supexp) $ tcError $ "expected support " ++ show supexp ++ " but got " ++ show sup
>   return supexp

> subsup :: Support -> Support -> Bool
> subsup (Support noms svs) (Support noms' svs') =
>   let nomsLeq = noms `isSubsequenceOf` noms'
>       svsLeq = svs `isSubsequenceOf` svs'
>   in nomsLeq && svsLeq

> checkExpr :: TC m => Expr -> Type -> m ()
> checkExpr e t = inferExpr_ e (Expecting (Just t)) >> return ()
> 

> inferExpr_ :: (TC m) => Expr -> Expected (Maybe Type) -> m Type
> inferExpr_ e0 xpt =
>   case e0 of
>     V x -> lookupVar x >>= expecting xpt
>     U noms u -> do
>       (t, supIn) <- lookupCodeVar u
>       checkSubst noms supIn
>       expecting xpt t
>     N nX -> do
>       t <- lookupNom nX
>       inSupport nX
>       expecting xpt t
>     C bc -> expecting xpt $ BaseT $ inferConst bc
>     P primOp vs es -> do
>       checkPrimitive primOp (vs ++ es) >>= expecting xpt
>     Lambda bnd -> do
>       ((x, unembed -> tDom), e) <- unbind bnd
>       wellFormed tDom
>       xptCod <- unExpectArrType xpt tDom
>       tCod <- extendVar x tDom $ inferExpr_ e xptCod
>       return (tDom `ArrT` tCod)
>     App e1 e2 -> do
>       tf <- inferExpr e1
>       (tDom, tCod) <- matchArrType tf
>       checkExpr e2 tDom
>       expecting xpt tCod
>     RecFun bnd -> do
>       ((f, x, unembed -> tDom, unembed -> tCod), e) <- unbind bnd
>       let funT = tDom `ArrT` tCod
>       extendVar f funT $ extendVar x tDom $ checkExpr e tCod
>       expecting xpt funT
>     Let e1 bnd -> do
>       t <- inferExpr e1
>       (x, e2) <- unbind bnd
>       extendVar x t $ inferExpr_ e2 xpt
>     Box c -> do
>       (xpt, xpsup) <- unExpectBoxType xpt
>       inferCode c xpt xpsup
>     LetBox e1 bnd -> do
>       tbox <- inferExpr e1
>       (t, sup) <- matchBoxType tbox
>       (u, e2) <- unbind bnd
>       extendCodeVar u t sup $ inferExpr_ e2 xpt
>     New bnd -> do
>       ((nX, unembed -> tDom), e) <- unbind bnd
>       wellFormed tDom
>       xptCod <- unExpectNomArrType xpt tDom
>       (tCod, supOut) <- withEmptySupport $ extendNom nX tDom $ inferExpr_ e xptCod
>       let inType = anyOf fv (== nX) tCod
>           inSup = anyOf fv (== nX) (supportNominals supOut)
>       when inType $ tcError ("Name " ++ show nX ++ " appears in the result type of a ν-expression " ++ show tCod)
>       when inSup $ tcError ("Name " ++ show nX ++ " appears in the support of ν-expression " ++ show supOut)
>       includeSupport supOut
>       return (tDom `NomArrT` tCod)
>     Choose e -> do
>       tarr <- inferExpr e
>       (_, tCod) <- matchNomArrType tarr
>       expecting xpt tCod
>     PLamSupport bnd -> do
>       (sv, e) <- unbind bnd
>       xptout <- unExpectForallSupType xpt sv 
>       (t, supOut) <- withEmptySupport $ extendSupportVar sv $ inferExpr_ e xptout
>       let inSup = anyOf fv (== sv) (supportVars supOut)
>       when inSup $ tcError ("support variable " ++ show sv ++ " appears in the support of the body of the support-polymorphic function")
>       includeSupport supOut
>       expecting xpt $ ForallSupT (bind sv t)
>     PAppSupport e sup -> do
>       tall <- inferExpr e
>       wellFormedSupport sup
>       (sv, t) <- matchForallSup tall
>       expecting xpt $ subst sv sup t

> inferCode :: TC m => Code -> Expected (Maybe Type) -> Expected (Maybe Support) -> m Type
> inferCode (Code e) xpt xpsup = do
>   (t, supOut) <- withEmptySupport (inferExpr_ e xpt)
>   BoxT t <$> expectingSup xpsup supOut

> matchArrType :: TC m => Type -> m (Type, Type)
> matchArrType (ArrT tdom tcod) = return (tdom, tcod)
> matchArrType t0 = tcError ("Expected an expression of function type, got " ++ show t0)

> matchNomArrType :: TC m => Type -> m (Type, Type)
> matchNomArrType (NomArrT tdom tcod) = return (tdom, tcod)
> matchNomArrType t0 = tcError ("Expected an expression of nominal-function type, got " ++ show t0)

> matchForallSup :: TC m => Type -> m (SupportVar, Type)
> matchForallSup (ForallSupT bnd) = unbind bnd
> matchForallSup t0 = tcError ("Expected a support-polymorphic type, got " ++ show t0)

> matchBoxType :: TC m => Type -> m (Type, Support)
> matchBoxType (BoxT t sup) = return (t, sup)
> matchBoxType t0 = tcError ("Expected an expression of code type, got " ++ show t0)

> unExpectArrType :: TC m => Expected (Maybe Type) -> Type -> m (Expected (Maybe Type))
> unExpectArrType (Expecting Nothing) _ = return (Expecting Nothing)
> unExpectArrType (Expecting (Just texp)) t' = do
>   (tdom, tcod) <- matchArrType texp
>   expecting (Expecting (Just tdom)) t'
>   return (Expecting (Just tcod))

> unExpectNomArrType :: TC m => Expected (Maybe Type) -> Type -> m (Expected (Maybe Type))
> unExpectNomArrType (Expecting Nothing) _ = return (Expecting Nothing)
> unExpectNomArrType (Expecting (Just texp)) t' = do
>   (tdom, tcod) <- matchNomArrType texp
>   expecting (Expecting (Just tdom)) t'
>   return (Expecting (Just tcod))

> unExpectForallSupType :: TC m => Expected (Maybe Type) -> SupportVar -> m (Expected (Maybe Type))
> unExpectForallSupType (Expecting Nothing) _ = return (Expecting Nothing)
> unExpectForallSupType (Expecting (Just texp)) sv = do
>   (sv', t) <- matchForallSup texp
>   return (Expecting (Just (swaps (PermM.single (AnyName sv) (AnyName sv')) t)))

> unExpectBoxType :: TC m => Expected (Maybe Type) -> m (Expected (Maybe Type), Expected (Maybe Support))
> unExpectBoxType (Expecting Nothing) = return (Expecting Nothing, Expecting Nothing)
> unExpectBoxType (Expecting (Just t)) = do
>   (t', sup) <- matchBoxType t
>   return (Expecting (Just t'), Expecting (Just sup))

> inferConst :: BaseConst -> BaseType
> inferConst UnitC = UnitT
> inferConst (BoolC _) = BoolT
> inferConst (IntC _) = IntT

> checkPrimitive :: TC m => PrimOp -> [Expr] -> m Type
> checkPrimitive (IfPrim t) [e, thunk1, thunk2] = do
>   wellFormed t
>   let thunkT = unitT `ArrT` t
>   checkExpr e boolT
>   checkExpr thunk1 thunkT
>   checkExpr thunk2 thunkT
>   return thunkT
> checkPrimitive (IfPrim _) es = tcError $ "if expression expected 2 branches, got " ++ show (length es)
> checkPrimitive AddPrim [e1,e2] = checkExpr e1 intT >> checkExpr e2 intT >> return intT
> checkPrimitive AddPrim es = binOpPrimitiveError AddPrim es
> checkPrimitive MulPrim [e1,e2] = checkExpr e1 intT >> checkExpr e2 intT >> return intT
> checkPrimitive MulPrim es = binOpPrimitiveError MulPrim es
> checkPrimitive LeqPrim [e1,e2] = checkExpr e1 intT >> checkExpr e2 intT >> return boolT
> checkPrimitive LeqPrim es = binOpPrimitiveError LeqPrim es
>
> binOpPrimitiveError :: TC m => PrimOp -> [Expr] -> m a
> binOpPrimitiveError p es = tcError $ "expected 2 arguments to " ++ show p ++ ", got " ++ show (length es)


> checkSubst :: (TC m) => NominalSubst -> Support -> m ()
> checkSubst = go . nominalSubst
>   where
>     go :: (TC m) => [(Nominal, Nom)] -> Support -> m ()
>     go [] = includeSupport
>     go ((nX, ne):noms) = \supIn -> do
>       t <- lookupNom nX
>       checkExpr (nomExpr ne) t
>       go noms (supIn `excludingNominal` nX)

> excludingNominal :: Support -> Nominal -> Support
> excludingNominal (Support noms svs) nX = Support (noms \\ [nX]) svs

> instance Monoid Support where
>   mempty = Support [] []
>   (Support noms svs) `mappend` (Support noms' svs') = Support noms'' svs''
>     where
>       noms'' = nub $ sort (noms ++ noms')
>       svs'' = nub $ sort (svs ++ svs')

> anyOf :: Fold s a -> (a -> Bool) -> s -> Bool
> anyOf l f =  getAny . foldMapOf l (Any . f)

> data Env = Env { envSigma :: NomCtx, envDelta :: [(CodeVar, Embed (Type, Support))], envGamma :: [(Var, Embed Type)] }

> newtype TypeCheck a = TypeCheck { unTypeCheck :: ReaderT Env (WriterT Support (ExceptT String FreshM)) a }
>                     deriving (Functor, Applicative, Monad, Fresh)

> hasSupportNomCtx :: SupportVar -> NomCtx -> Bool
> hasSupportNomCtx  _ NilNC = False
> hasSupportNomCtx sv (SnocNC (unrebind -> (ctx, _))) = hasSupportNomCtx sv ctx
> hasSupportNomCtx sv (SnocSupNC (ctx, sv')) | sv == sv' = True
>                                            | otherwise = hasSupportNomCtx sv ctx
>   

> lookupNominalNomCtx :: Nominal -> NomCtx -> Maybe (Embed Type)
> lookupNominalNomCtx _ NilNC = Nothing
> lookupNominalNomCtx nX (SnocNC (unrebind -> (ctx, (nY, t)))) | nX == nY = Just t
>                                                              | otherwise = lookupNominalNomCtx nX ctx
> lookupNominalNomCtx nX (SnocSupNC (ctx, _)) = lookupNominalNomCtx nX ctx

> instance TC TypeCheck where
>   lookupSupportVar sv = do
>     b <- TypeCheck $ asks (hasSupportNomCtx sv . envSigma)
>     unless b $ tcError ("Support variable " ++ show sv ++ " not in scope")
>   lookupVar x = do
>     m <- TypeCheck $ asks (lookup x . envGamma)
>     case m of
>       Just t -> return (unembed t)
>       Nothing -> tcError ("Variable " ++ show x ++ " not in scope")
>   lookupCodeVar u = do
>     m <- TypeCheck $ asks (lookup u . envDelta)
>     case m of
>       Just ts -> return (unembed ts)
>       Nothing -> tcError ("Code variable " ++ show u ++ " not in scope")
>   lookupNom nX = do
>     m <- TypeCheck $ asks (lookupNominalNomCtx nX . envSigma)
>     case m of
>       Just t -> return (unembed t)
>       Nothing -> tcError ("Nominal " ++ show nX ++ " not in scope")
>   extendVar x t = TypeCheck . local (\env -> env { envGamma = (x, embed t) : envGamma env  }) . unTypeCheck
>   extendCodeVar u t sup = TypeCheck . local (\env -> env { envDelta = (u, embed (t, sup)) : envDelta env } ) . unTypeCheck
>   extendNom nX t = TypeCheck . local (\env -> env { envSigma = SnocNC (rebind (envSigma env) (nX, embed t)) } ) . unTypeCheck
>   extendSupportVar sv = TypeCheck . local (\env -> env { envSigma = SnocSupNC (envSigma env, sv) } ) . unTypeCheck
> 
>   tcError = TypeCheck . throwError
>
>   includeSupport = TypeCheck . tell
>
>   withEmptySupport comp =
>     let censorEverything = const mempty
>     in TypeCheck (pass ((\asup -> (asup, censorEverything)) <$> listen (unTypeCheck comp)))

> inferClosedConfig :: TC m => ClosedConfig -> m Type
> inferClosedConfig bnd = do
>   (ctx, expr) <- unbind bnd
>   inferConfiguration ctx expr

> inferConfiguration :: TC m => NomCtx -> Expr -> m Type
> inferConfiguration ctx = inWellFormedNomCtx ctx . inferExpr

> inWellFormedNomCtx :: TC m => NomCtx -> m a -> m a
> inWellFormedNomCtx NilNC = id
> inWellFormedNomCtx (SnocNC (unrebind -> (ctx, (nX, unembed -> t)))) = \k ->
>   inWellFormedNomCtx ctx $ do
>   wellFormed t
>   extendNom nX t k
> inWellFormedNomCtx (SnocSupNC (ctx,sv)) = inWellFormedNomCtx ctx . extendSupportVar sv 

> runTypeCheck :: TypeCheck a -> Either String (a, Support)
> runTypeCheck comp = runFreshM (runExceptT (runWriterT (runReaderT (unTypeCheck comp) emptyEnv)))
>   where emptyEnv = Env emptySigma emptyDelta emptyGamma
>         emptySigma = NilNC
>         emptyDelta = []
>         emptyGamma = []

Appendix: Pretty Printing
==========================

We need our own pretty printer class because we want locally fresh
names when we descened under binders.

> type Precedence = Int

> class Pretty a where
>   pp :: LFresh m => a -> Precedence -> m PP.Doc

> paren :: Functor m => Bool -> m PP.Doc -> m PP.Doc
> paren b = if b then fmap PP.parens else id

> lowest, quantBodyPrec, arrPrec, arrPrecLeft, boxPrec, quantPrec :: Precedence
> lowest = -1
> quantBodyPrec = 2
> arrPrec = 5
> arrPrecLeft = 6
> boxPrec = 9
> quantPrec = 2

> lamBodyPrec, appPrec :: Precedence
> semiPrec = 1
> letBodyPrec = 1
> lamBodyPrec = 2
> leqPrec = 3
> addPrec = 4
> addPrecRight = 5
> mulPrec = 5
> mulPrecRight = 6
> lambdaPrec = 7
> letPrec = 7
> bindingPrec = 8
> appPrec = 10

> instance Pretty BaseType where
>   pp b _p = pure $ PP.text $ case b of
>     UnitT -> "()"
>     BoolT -> "bool"
>     IntT  -> "int"

> instance Pretty Type where
>   pp t0 p = case t0 of
>     BaseT b -> pp b lowest
>     ArrT t1 t2 -> paren (p > arrPrec) (infixBinary <$> pp t1 arrPrecLeft <*> pure (PP.text "→") <*> pp t2 arrPrec)
>     NomArrT t1 t2 -> paren (p > arrPrec) (infixBinary <$> pp t1 arrPrecLeft <*> pure (PP.text "↛") <*> pp t2 arrPrec)
>     BoxT t sup -> paren (p > boxPrec) (ppboxType <$> pp t boxPrec <*> pp sup lowest)
>     ForallSupT bnd -> paren (p > quantPrec) (quantifier "∀" <$> lunbind bnd (\(sv, t) -> (,) <$> pp sv lowest <*> pp t quantBodyPrec))

> instance Pretty Support where
>   pp (Support noms svs) _dk = ppsupport <$> traverse (fmap decorNominal . flip pp lowest) noms <*> traverse (fmap decorSupportVar . flip pp lowest) svs

> decorSupportVar :: PP.Doc -> PP.Doc
> decorSupportVar = PP.dullblue

> decorCodeVar :: PP.Doc -> PP.Doc
> decorCodeVar = PP.dullmagenta

> decorNominal :: PP.Doc -> PP.Doc
> decorNominal = PP.bold

> instance Pretty (Name a) where
>   pp a _dk = pure $ PP.text $ show a

> ppboxType :: PP.Doc -> PP.Doc -> PP.Doc
> ppboxType t sup = PP.hang 2 (PP.text "□_" PP.<> sup PP.</> PP.group t)

> ppsupport :: [PP.Doc] -> [PP.Doc] -> PP.Doc
> ppsupport noms svs = PP.group $ PP.hang 2 $ PP.braces $ PP.fillSep $ PP.punctuate PP.comma (noms ++ svs)


> infixBinary :: PP.Doc -> PP.Doc -> PP.Doc -> PP.Doc
> infixBinary p1 s p2 = PP.group $ PP.fillSep [p1, s, p2]

> quantifier :: String -> (PP.Doc, PP.Doc) -> PP.Doc
> quantifier q (obj, body) = PP.text q PP.<//> obj PP.<//> PP.dot PP.<//> body

> instance Pretty Expr where
>   pp e0 p = case e0 of
>     V x -> pp x lowest
>     U subs u -> (PP.<>) <$> pp subs lowest <*> (fmap decorCodeVar . flip pp lowest) u
>     N nom -> decorNominal <$> pp nom lowest
>     C c -> pp c lowest
>     P prim vs es -> paren (p > primPrecedence prim) (ppPrimitive prim (vs ++ es))
>     Lambda bnd -> paren (p > lambdaPrec) (pplambda "λ" <$> lunbind bnd (\((x, unembed -> t), e) -> (,) <$> (colonclass <$> pp x lowest <*> pp t lowest) <*> pp e lamBodyPrec))
>     RecFun bnd -> paren (p > lambdaPrec) (pprecfun <$> lunbind bnd (\((f, x, unembed -> targ, unembed -> tres), e) -> (,,,,) <$> pp f lowest <*> pp x lowest <*> pp targ lowest <*> pp tres lowest <*> pp e lamBodyPrec ))
>     App e1 e2 -> paren (p > appPrec) (ppapp <$> pp e1 appPrec <*> pp e2 (appPrec + 1))
>     Let e1 bnd -> paren (p > letPrec) (pplet PP.empty <$> pp e1 bindingPrec <*> lunbind bnd (\(x, e2) -> (,) <$> pp x lowest <*> pp e2 letBodyPrec))
>     LetBox e1 bnd -> paren (p > letPrec) (pplet (PP.text "□") <$> pp e1 bindingPrec <*> lunbind bnd (\(u, e2) -> (,) <$> (fmap decorCodeVar . flip pp lowest) u <*> pp e2 letBodyPrec))
>     Box code -> pp code lowest
>     New bnd -> paren (p > lambdaPrec) (pplambda "ν" <$> lunbind bnd (\((nX, unembed -> t), e) -> (,) <$> ppnombind nX t <*> pp e lamBodyPrec))
>     Choose e -> paren (p > appPrec) (ppapp (PP.text "choose") <$> pp e appPrec)
>     PLamSupport bnd -> paren (p > lambdaPrec) (pplambda "Λ" <$> lunbind bnd (\(sv, e) -> (,) <$> (fmap decorSupportVar . flip pp lowest) sv <*> pp e lamBodyPrec))
>     PAppSupport e sup -> paren (p > appPrec) (PP.nest 2 <$> ((PP.</>) <$> (fmap PP.group . flip pp appPrec) e <*> pp sup lowest))

> ppnombind nX t = assocclass <$> fmap decorNominal (pp nX lowest) <*> pp t lowest

> instance Pretty Code where
>   pp (Code e) _dk = ppcode <$> pp e lowest
>     where
>       ppcode c = PP.enclose (PP.text "“") (PP.text "”") (PP.underline c)

> instance Pretty BaseConst where
>   pp bc _dk = pure $ case bc of
>     UnitC -> PP.text "()"
>     BoolC b -> PP.text $ show b
>     IntC i -> PP.int i

> primPrecedence :: PrimOp -> Precedence
> primPrecedence (IfPrim _) = appPrec
> primPrecedence AddPrim = addPrec
> primPrecedence MulPrim = mulPrec
> primPrecedence LeqPrim = leqPrec
>
> ppPrimitive :: LFresh m => Pretty a => PrimOp -> [a] -> m PP.Doc
> ppPrimitive (IfPrim t) es = do
>   let prettyExpr = fmap PP.group . flip pp semiPrec
>   pes <- traverse prettyExpr es
>   pt <- pp t lowest
>   return $ PP.group (PP.text "if" PP.</> (PP.parens $ PP.group $ PP.align $ PP.vsep $ PP.punctuate PP.semi (pt:pes)))
> ppPrimitive AddPrim [e1,e2] = infixBinary <$> pp e1 addPrec <*> pure (PP.text "+") <*> pp e2 addPrecRight
> ppPrimitive MulPrim [e1,e2] = infixBinary <$> pp e1 mulPrec <*> pure (PP.text "*") <*> pp e2 mulPrecRight
> ppPrimitive LeqPrim [e1,e2] = infixBinary <$> pp e1 leqPrec <*> pure (PP.text "≤") <*> pp e2 leqPrec
> ppPrimitive _ _ = error "cant' happen (in well-typed code)"

> colonclass :: PP.Doc -> PP.Doc -> PP.Doc
> colonclass v clas = v PP.<//> PP.colon PP.<//> clas

> assocclass :: PP.Doc -> PP.Doc -> PP.Doc
> assocclass v clas = v PP.<//> PP.text "∼" PP.<//> clas

> pplambda :: String -> (PP.Doc, PP.Doc) -> PP.Doc
> pplambda lam (vclas, body) = PP.group $ PP.align $ PP.vsep [PP.group (PP.vcat [PP.text lam, vclas, PP.dot]), PP.group body]

> ppapp :: PP.Doc -> PP.Doc -> PP.Doc
> ppapp e1 e2 = PP.group $ PP.align $ PP.vsep [PP.group e1, PP.nest 2 (PP.group e2)]

> pprecfun :: (PP.Doc, PP.Doc, PP.Doc, PP.Doc, PP.Doc) -> PP.Doc
> pprecfun (f, x, targ, tres, e) = PP.group $ PP.hang 2 $ PP.vsep [PP.text "rec", PP.group (PP.sep [f, binding, PP.colon, tres]), PP.group (PP.text "is" PP.</> PP.nest 2 (PP.group e))]
>   where
>     binding = PP.parens (colonclass x targ)

> pplet :: PP.Doc -> PP.Doc -> (PP.Doc, PP.Doc) -> PP.Doc
> pplet unclas e1 (x,e2) = PP.fillSep [PP.text "let", PP.hang 2 binding] PP.</> PP.group (PP.hang 2 (PP.text "in" PP.</> PP.nest 2 e2))
>   where
>     binding = PP.group (PP.fillSep [unclas PP.<//> x, PP.text "="] PP.</> PP.hang 2 e1)

> instance Pretty NominalSubst where
>   pp (NominalSubst subs) _dk =
>     ppsubstitution <$> traverse ppsub subs
>     where
>       ppsubstitution = PP.enclose (PP.text "⟨") (PP.text "⟩") . PP.fillSep . PP.punctuate PP.comma
>       ppsub (nX, nom) = mapto <$> (fmap decorNominal . flip pp lowest) nX <*> pp nom lowest
>       mapto nX nom = PP.group (nX PP.</> PP.text "↦") PP.</> nom

> instance Pretty Nom where
>   pp = pp . nomExpr

> pretty :: Pretty a => a -> String
> pretty a = flip PP.displayS "" $ PP.renderSmart 0.8 80 $ runLFreshM $ pp a lowest

> ppretty :: Pretty a => a -> IO ()
> ppretty a = do
>   PP.displayIO IO.stdout $ PP.renderSmart 0.8 80 $ runLFreshM $ pp a lowest
>   putStrLn ""

Example
-------

> -- >>> ppretty (pexp @@ number 3)
> -- (λn:int.
> -- choose
> --  (νX∼int.
> --   let □w = (Λp.
> --             λe:□_{p} int.
> --             rec
> --               go (m:int) : □_{p} int
> --               is if (□_{p} int;
> --                      m ≤ 0;
> --                      λ_:(). “1”;
> --                      λ_:(). let □u = go (m + -1) in let □w = e in “⟨⟩u * ⟨⟩w”)
> --                  ()) {X}
> --            “X”
> --            n in “λx:int. ⟨X ↦ x⟩w”))
> -- 3

Appendix: Tracing evaluator
===========================

> instance Pretty NomCtx where
>   pp NilNC _ = pure PP.empty
>   pp (SnocNC (unrebind -> (NilNC, (nX, unembed -> t)))) _ = ppnombind nX t
>   pp (SnocNC (unrebind -> (ctx, (nX, unembed -> t)))) _ = (PP.</>) <$> fmap (\pctx -> pctx PP.</> PP.comma) (pp ctx lowest) <*> ppnombind nX t
>   pp (SnocSupNC (NilNC, sv)) _ = decorSupportVar <$> pp sv lowest
>   pp (SnocSupNC (ctx, sv)) _ = (PP.</>) <$> fmap (\pctx -> pctx PP.</> PP.comma) (pp ctx lowest) <*> (decorSupportVar <$> pp sv lowest)

> data WellTypedProgram = WellTypedProgram NomCtx Expr Type Support
>
> instance Pretty WellTypedProgram where
>   pp (WellTypedProgram ctx e t sup) _ = do
>     pctx <- pp ctx lowest
>     pe <- pp e lowest
>     pt <- pp t lowest
>     psup <- pp sup lowest
>     return $ PP.group $ PP.vcat [pctx, PP.text "⊢", pe, PP.nest 2 PP.colon, PP.nest 4 pt, PP.nest 4 psup]

> traceProgram :: Expr -> IO ()
> traceProgram initialExpr = do
>   let tc ctx e = case runTypeCheck (inferConfiguration ctx e) of
>         Right (t, sup) -> ppretty (WellTypedProgram ctx e t sup)
>         Left err -> putStrLn err >> fail "(Not running)"
>   let
>     trace :: (Fresh m, MonadState NomCtx m, MonadError String m, MonadIO m) => Expr -> m ()
>     trace e =
>         if isValue e
>         then return ()
>         else
>         do
>           e' <- step e
>           ctx <- get
>           liftIO $ do
>             tc ctx e'
>             putStrLn "————"
>           trace e'
>   tc NilNC initialExpr
>   putStrLn "————"
>   _ <- runFreshMT (runExceptT (runStateT (trace initialExpr) NilNC))
>   return ()
> _ = ()


