This example is based on ``Staged Computation with Names and Necessity'' by Nanevski and Pfenning.

> {-# language DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses,
>     FlexibleContexts, FlexibleInstances #-}
> module Nanevski where
>
> import GHC.Generics (Generic)
> import Data.Typeable (Typeable)
> import Unbound.Generics.LocallyNameless
> import Control.Monad.Except
> import Control.Monad.State

\section{Syntax}

\subsection{Types}

> data BaseType = UnitT | BoolT | IntT
>   deriving (Typeable, Generic, Show)

> data Type =
>   BaseT BaseType          -- some base types
>   | ArrT Type Type        -- τ₁→τ₂ functions
>   | BoxT Type [Nominal]   -- □_C τ is the type of code of type τ with names in C
>   | NomArr Type Type      -- τ₁ ↛ τ₂ is the type of νN:τ₁.e brings a
>                           -- new name N associated with type τ₁ into
>                           -- scope in a body of type τ₂.  The new
>                           -- name cannot appear in the type τ₂ or in
>                           -- the support of e.  It is thus
>                           -- guaranteed to either be substituted
>                           -- away or only appear in code in e, not
>                           -- in subexpresisons that may be evaluated
>                           -- in teh course of evaluating e.
>   deriving (Typeable, Generic, Show)

\subsection{Expressions}

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
>   deriving (Typeable, Generic, Show)
>
> data BaseConst = UnitC | BoolC !Bool | IntC !Int
>   deriving (Typeable, Generic, Show)
> data PrimOp = IfPrim | AddPrim | MulPrim | LeqPrim
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
> isValue _ = False

\subsection{Code}

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

\subsection{Nominals}

A Nominal can appear in code (but not in an expression that may be
evaluated).  It stands for an expression just like Var, but in
unbound-generics since we want to treat Nominal and Var distinctly, we
add a newtype wrapper around Expr and call it a Nom.

> newtype Nom = Nom {nomExpr :: Expr }
>   deriving (Typeable, Generic, Show)
> type Nominal = Name Nom

\subsection{Alpha renaming, free names, alpha-equivalence boilerplate}

All the types we defined will participate in various Alpha operations:
we can collect the free Variabes, Nominals or CodeVars of all the
syntactic categories.  They are also subject to alpha equivalence upto
renaming of bound occurrances, etc.

> instance Alpha Nom
> instance Alpha Code
> instance Alpha NominalSubst
> instance Alpha Type
> instance Alpha Expr
> instance Alpha BaseType
> instance Alpha BaseConst
> instance Alpha PrimOp

\subsection{Substitutions}

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
> instance Subst a PrimOp where
>   subst _ _ = id
>   substs _ = id

\subsubsection{Expression substitution}

Ordinary variables can occur in expressions as well as code, noms and
nominal substitutions.  They don't occur in types, so we can
short-circuit substitution there and return the type unchanged.

> instance Subst Expr Type where
>   subst _ _ = id
>   substs _ = id
> instance Subst Expr Expr where
>   isvar (V v) = Just (SubstName v)
>   isvar _ = Nothing
> instance Subst Expr Code
> instance Subst Expr NominalSubst
> instance Subst Expr Nom

\subsubsection{Nominal substitution}

> instance Subst Nom Nom

To substitute for a nominal N in an expression e, we use need to use
\texttt{isCoerceVar} to pull out the expression from the Nom being
substituted.

> instance Subst Nom Expr where
>   isCoerceVar (N n) = Just $ SubstCoerce n (Just . nomExpr)
>   isCoerceVar _ = Nothing

An important property (justified by the type system) of this language
is that when substituting for a name N in an expression Box (Code e)
we can just return Box (Code e) unchanged.

> instance Subst Nom Code where
>   subst _ _ = id
>   substs _ = id

> instance Subst Nom Type
> instance Subst Nom NominalSubst

\subsubsection{Code substitution}

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

\section{Operational Semantics}

The operational semantics take configurations consisting of a context
of Nominals together with their associated types and an expression
with empty support to another such configuration.

> data NomCtx = NilNC | SnocNC (Rebind NomCtx (Nominal, Embed Type))
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

> evalError :: MonadError String m => String -> m a
> evalError = throwError

> applyPrim :: MonadError String m => PrimOp -> [Value] -> m Value
> applyPrim IfPrim [C (BoolC b), v1, v2] = return $ if b then v1 else v2
> applyPrim AddPrim [C (IntC x), C (IntC y)] = return $ C $ IntC $ x + y
> applyPrim MulPrim [C (IntC x), C (IntC y)] = return $ C $ IntC $ x * y
> applyPrim LeqPrim [C (IntC x), C (IntC y)] = return $ C $ BoolC $ x <= y
> applyPrim p vs = evalError (show p ++ show vs ++ " does not step")

> eval :: (Fresh m, MonadState NomCtx m, MonadError String m) => Expr -> m Expr
> eval e = if isValue e then return e else step e >>= eval
  
\subsection{Example}

\subsubsection{A little DSL for term construction}

> lam :: String -> Type -> (Expr -> Expr) -> Expr
> lam s t f =
>   let x = s2n s
>   in Lambda $ bind (x, embed t) (f $ V x)

> recFun :: String -> String -> Type -> Type -> (Expr -> Expr -> Expr) -> Expr
> recFun sfn sx t1 t2 f =
>   let fn = s2n sfn
>       x = s2n sx
>   in RecFun $ bind (fn, x, embed t1, embed t2) (f (V fn) (V x))

> intT, unitT :: Type
> intT = BaseT IntT
> unitT = BaseT UnitT


> (@@) :: Expr -> Expr -> Expr
> (@@) = App
> infixr 5 @@

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

> ifLeqZ :: Expr -> Expr -> Expr -> Expr
> ifLeqZ ex etrue efalse =
>   App (P IfPrim [] [etest, thunk etrue, thunk efalse]) (C UnitC)
>   where
>     etest = P LeqPrim [] [ex, number 0]
>     thunk e = lam "_" unitT (\_ -> e)

> sub1 :: Expr -> Expr
> sub1 e = P AddPrim [] [e, number (-1)]

> mul :: Expr -> Expr -> Expr
> mul e1 e2 = P MulPrim [] [e1, e2]

> (~~) :: a -> b -> (a, b)
> (~~) = (,)
> infix 5 ~~

\subsubsection{Staged exponential function}

(Note that within the calculus itself there's not a way to abstract over a nominal like this - the example below chooses a new X which appears in the definition of this helper function.)

First a little recursive helper function that expands out to the m-fold multiplication code \texttt{X * X * X * ... * 1}

> exp' :: Nominal -> Expr
> exp' nX = recFun "exp'" "m" intT intT $ \exp' m ->
>   ifLeqZ m (box $ number 1) (letBox "u" (exp' @@ (sub1 m)) $ \u ->
>                                 box $ mul (name nX) (runCode u))
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

\begin{verbatim}
λ> run (eval (expon @@ number 3))
Right (Box (Code {codeExpr = Lambda (<(x,{BaseT IntT})> P MulPrim [] [V 0@0,P MulPrim [] [V 0@0,P MulPrim [] [V 0@0,C (IntC 1)]]])}),SnocNC (<<NilNC>> (X1,{BaseT IntT})))
\end{verbatim}

\begin{verbatim}
λ> run (eval (letBox "exp3" (expon @@ number 3) $ \exp3 -> (runCode exp3) @@ number 2))
Right (C (IntC 8),SnocNC (<<NilNC>> (X1,{BaseT IntT})))
\end{verbatim}
