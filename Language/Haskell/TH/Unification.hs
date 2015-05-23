{-# LANGUAGE CPP, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, StandaloneDeriving, GeneralizedNewtypeDeriving #-}

module Language.Haskell.TH.Unification (subTerm, Term(..), MonadUnify(..), UnifT, Explicit(..), solveUnification) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (Applicative)
#endif
import Control.Monad
import Data.Map hiding (map)
import Control.Monad.State.Strict
import Control.Monad.Except

data Term f v a = App f (Term f v a) (Term f v a) | Atom a | Var v deriving (Eq, Show)
data Explicit f a = AppE f (Explicit f a) (Explicit f a) | AtomE a deriving (Eq, Show)
type Solution f v a = Map v (Explicit f a)

data Constraint f v a = Term f v a :==: Term f v a
type Constraints f v a = [Constraint f v a]

newtype UnifT f v a m x = UnifT (StateT (Constraints f v a) (ExceptT String m) x)
deriving instance Functor m => Functor (UnifT f v a m)
deriving instance (Monad m, Functor m) => Applicative (UnifT f v a m)
deriving instance (Monad m) => Monad (UnifT f v a m)
deriving instance (Monad m) => MonadState (Constraints f v a) (UnifT f v a m)

class Monad m => MonadUnify u m | m -> u where
	unify :: u -> u -> m ()

instance Monad m => MonadUnify (Term f v a) (UnifT f v a m) where
	a `unify` b = modify ((a :==: b):)

instance MonadUnify u m => MonadUnify u (StateT s m) where
	a `unify` b = lift (a `unify` b)

instance MonadTrans (UnifT f v a) where
	lift = UnifT . lift . lift

runUnification :: (Ord v, Eq f, Eq a, Monad m) => UnifT f v a m x -> m (Either String (Constraints f v a))
runUnification (UnifT m) = runExceptT (execStateT m [])

solveUnification :: (Ord v, Eq f, Eq a, Monad m) => Explicit f a -> UnifT f v a m x -> m (Either String (x, Solution f v a))
solveUnification def (UnifT m) = runExceptT (evalStateT m' [])
	where	m' = do	x <- m
			ans <- solve def =<< get
			return (x, ans)

solve :: (Ord v, Eq f, Eq a, Monad m) => Explicit f a -> Constraints f v a -> m (Solution f v a)
solve def (constr:constrs) = case constr of
	Var x :==: Var y
		| x == y	-> solve def constrs
	Var x :==: t
		-> subSol def x t `liftM` solve def (substitute x t constrs)
	t :==: Var y
		-> subSol def y t `liftM` solve def (substitute y t constrs)
	Atom a :==: Atom b
		| a == b	-> solve def constrs
		| otherwise	-> fail "Mismatched atoms"
	App f1 x1 y1 :==: App f2 x2 y2
		| f1 == f2	-> solve def ([x1 :==: x2, y1 :==: y2] ++ constrs)
		| otherwise	-> fail "Mismatched functions"
	_	-> fail "Function matched to atom"
solve _ [] = return empty

substitute :: (Ord v, Eq f, Eq a) => v -> Term f v a -> Constraints f v a -> Constraints f v a
substitute v t = map (\ (x :==: y) -> sub x :==: sub y) where
	sub (Var v')
		| v == v'	= t
	sub (App f x y) = App f (sub x) (sub y)
	sub t' = t'

subTerm :: Ord v => Explicit f a -> Solution f v a -> Term f v a -> Explicit f a
subTerm def sol (Var v) = findWithDefault def v sol
subTerm def sol (App f x y) = AppE f (subTerm def sol x) (subTerm def sol y)
subTerm _ _ (Atom a) = AtomE a

subSol :: (Ord v, Eq f, Eq a) => Explicit f a -> v -> Term f v a -> Solution f v a -> Solution f v a
subSol def v t sol = insert v (subTerm def sol t) sol
