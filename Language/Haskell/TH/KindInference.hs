{-# LANGUAGE CPP #-}

-- | A module to infer the kind of a given type within Template Haskell.
-- Warning: this implements its own kind inference system, and is therefore
-- not guaranteed to work on all esoteric types.  (That said, I have no examples
-- where it doesn't work.)
module Language.Haskell.TH.KindInference (inferKind) where

-- import Control.Monad
import Control.Monad.Trans
import Data.Set hiding (foldr)
import Control.Monad.State.Strict
import Text.ParserCombinators.ReadP hiding (get)

import Language.Haskell.TH hiding (AppE)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Unification
import Language.Haskell.TH.PprLib hiding (empty, char)
import qualified Language.Haskell.TH.PprLib as Ppr

type KindUTerm = Term KindFunc Type KindAtom
type KindUT = UnifT KindFunc Type KindAtom

type LoopKillerT = StateT (Set Name)
data KindFunc = KindArrow deriving (Eq, Ord, Show)
data KindAtom = Star deriving (Eq, Ord, Show)

-- | Returns either an error message or the 'Kind' of the type referred to by the specified name.
-- Works with datas, newtypes, type synonyms, type classes, data families, and type families.
-- 
-- Note: There has been a bug observed in Template Haskell relating to the parsing of types.  This
-- assumes that bug has been fixed, requiring GHC at least 6.12.2.
class InferKind t where
    inferKind :: t -> Q (Either String Kind)

instance InferKind Name where
    inferKind name = inferKind (ConT name)

instance InferKind Type where
    inferKind typ = do
      ans <- solveUnification defaultKind (evalStateT (infer typ) empty)
      either (return . Left) (\ (x, sol) -> return (Right $ termToK (subTerm defaultKind sol x))) ans

defaultKind :: Explicit KindFunc KindAtom
defaultKind = AtomE Star

termToK :: Explicit KindFunc KindAtom -> Kind
#if MIN_VERSION_template_haskell(2,8,0)
-- Kind became a synonym of Type here
termToK (AppE ~KindArrow t1 t2) = termToK t1 `AppT` termToK t2
#else
termToK (AppE ~KindArrow t1 t2) = termToK t1 `ArrowK` termToK t2
#endif
termToK (AtomE ~Star) = StarT

infer :: Type -> LoopKillerT (KindUT Q) KindUTerm
infer (TupleT n) = return (tupleKind n star)
infer ArrowT = return (tupleKind 2 star)
infer ListT = return (tupleKind 1 star)
infer (AppT f x) = do
        fK <- infer f
        xK <- infer x
        let var = Var (AppT f x)
        unify fK (xK ->- var)
        return var
infer (SigT t k) = do
        tK <- infer t
        unify tK (kToTerm k)
        return tK
infer (ForallT bdrs cxt t) = do
        mapM_ handleBdr bdrs
        mapM_ handleCxt cxt
        infer t
infer t@VarT{} = return $ Var t
infer (ConT t) = do
        examine (Just t) t
        return (tyCon t)
infer t = error $ "inferKind - unimplemented: " ++ pprint t

matchUnboxedTuple :: ReadP Int
matchUnboxedTuple = do
        string "(#"
        munchComma 1
        where   munchComma k = k `seq` ((do
                        char ','
                        munchComma (k+1)) <++ (do
                        string "#)"
                        return k))

examine :: Maybe Name -> Name -> LoopKillerT (KindUT Q) ()
examine name0 name = do
     mUnify name0 (tyVar name)
     case [n | (n, "") <- readP_to_S matchUnboxedTuple (nameBase name)] of
        (n:_)   -> unify (tyVar name) (tupleKind n star)
        _       -> do
          inf <- lift $ lift $ reify name
          case inf of
#if MIN_VERSION_template_haskell(2,5,0)
                  ClassI dec _is -> examineDec name0 dec
#else
                  ClassI dec    -> examineDec name0 dec
#endif
                  TyConI dec    -> examineDec name0 dec
                  PrimTyConI name n _ -> unify (tyVar name) (tupleKind n star)
                  TyVarI name typ -> do
                        kind <- infer typ
                        unify (tyVar name) kind
                  FamilyI dec insts -> do
                        examineDec name0 dec
                  _ -> return ()

mUnify :: Maybe Name -> KindUTerm -> LoopKillerT (KindUT Q) ()
mUnify name0 k = case name0 of
        Just name0      -> unify (tyCon name0) k
        _               -> return ()

examineDec :: Maybe Name -> Dec -> LoopKillerT (KindUT Q) ()
examineDec name0 (DataD cxt name bdrs cons _) = do
        visited <- get
        unless (name `member` visited) $ do
          modify (insert name)
          mapM_ handleCxt cxt
          args <- mapM handleBdr bdrs
          unify (tyCon name) (foldr (->-) star args)
          mUnify name0 (tyCon name)
          mapM_ handleCon cons
examineDec name0 (NewtypeD cxt name bdrs con _) = do
        visited <- get
        unless (name `member` visited) $ do
          modify (insert name)
          mapM_ handleCxt cxt
          args <- mapM handleBdr bdrs
          unify (tyCon name) (foldr (->-) star args)
          mUnify name0 (tyCon name)
          handleCon con
examineDec name0 (ClassD cxt name bdrs _ _) = do
        visited <- get
        unless (name `member` visited) $ do
          modify (insert name)
          mapM_ handleCxt cxt
          args <- mapM handleBdr bdrs
          unify (tyCon name) (foldr (->-) star args)
          mUnify name0 (tyCon name)
examineDec name0 (FamilyD _ name bdrs mK) = do
        visited <- get
        unless (name `member` visited) $ do
          modify (insert name)
          args <- mapM handleBdr bdrs
          unify (tyCon name) (foldr (->-) (maybe star kToTerm mK) args)
          mUnify name0 (tyCon name)
examineDec name0 (TySynD name bdrs typ) = do
        visited <- get
        unless (name `member` visited) $ do
          modify (insert name)
          args <- mapM handleBdr bdrs
          kind <- infer typ
          unify (tyCon name) (foldr (->-) kind args)
          mUnify name0 (tyCon name)
examineDec _ _ = return ()

handleCon :: Con -> LoopKillerT (KindUT Q) ()
handleCon (NormalC _ ts) = mapM_ (\ (_, t) -> infer t >>= unify star) ts
handleCon (RecC _ ts) = mapM_ (\ (_, _, t) -> infer t >>= unify star) ts
handleCon (InfixC (_, t1) _ (_, t2)) = do
        infer t1 >>= unify star
        infer t2 >>= unify star
handleCon (ForallC bdrs cxt con) = do
        mapM_ handleBdr bdrs
        mapM_ handleCxt cxt
        handleCon con

tyCon :: Name -> KindUTerm
tyCon = Var . ConT

tyVar :: Name -> KindUTerm
tyVar = Var . VarT

handleBdr :: TyVarBndr -> LoopKillerT (KindUT Q) KindUTerm
handleBdr (PlainTV n) = return (tyVar n)
handleBdr (KindedTV n k) = do
        unify (tyVar n) (kToTerm k)
        return (tyVar n)

handleCxt :: Pred -> LoopKillerT (KindUT Q) ()
#if MIN_VERSION_template_haskell(2,10,0)
handleCxt typ =
        case unfoldInstance typ of
          Just (name, args) -> do
            kinds <- mapM infer args
            unify (Var (ConT name)) (foldr (->-) star kinds)
            examine (Just name) name
        where
          unfoldInstance :: Type -> Maybe (Name, [Type])
          unfoldInstance (ConT name) = Just (name, [])
          unfoldInstance (AppT t1 t2) = maybe Nothing (\ (name, types) -> Just (name, types ++ [t2])) (unfoldInstance t1)
          unfoldInstance _ = Nothing
handleCxt (AppT (AppT EqualityT t1) t2) = do
        k1 <- infer t1
        k2 <- infer t2
        unify k1 k2
#else
handleCxt (ClassP name args) = do
        kinds <- mapM infer args
        unify (Var (ConT name)) (foldr (->-) star kinds)
        examine (Just name) name
handleCxt (EqualP t1 t2) = do
        k1 <- infer t1
        k2 <- infer t2
        unify k1 k2
#endif

kToTerm :: Kind -> KindUTerm
#if MIN_VERSION_template_haskell(2,8,0)
kToTerm (AppT a b) = kToTerm a ->- kToTerm b
kToTerm StarT = star
#else
kToTerm (ArrowK a b) = kToTerm a ->- kToTerm b
kToTerm StarK = star
#endif

(->-) :: KindUTerm -> KindUTerm -> KindUTerm
(->-) = App KindArrow

star :: KindUTerm
star = Atom Star

tupleKind :: Int -> KindUTerm -> KindUTerm
tupleKind n k = foldr (->-) k (replicate n star)

instance (Ppr a, Ppr b) => Ppr (Either a b) where
        ppr (Left x) = text "Left" <+> parens (ppr x)
        ppr (Right x) = text "Right" <+> parens (ppr x)
instance Ppr Char where
        ppr = Ppr.char
