{-# OPTIONS_GHC
    -Wincomplete-patterns
    -Woverlapping-patterns
#-}
{-# LANGUAGE LambdaCase #-}

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Error.Class

type Zmod = Int

data LType = Unit | Sum LType LType | Arrow LType LType
    deriving (Eq)

newtype Variable = Variable Int
    deriving (Eq, Ord, Num)
newtype Constant = Constant Int
    deriving (Eq, Ord, Num)

data LExpr =
    Var Variable
  | Zero LType
  | Plus LExpr LExpr
  | Const Constant
  | Scale LExpr LExpr

  | Pair LExpr LExpr
  | Case LExpr Variable LExpr Variable LExpr

  | Lambda Variable LType LExpr
  | Apply LExpr LExpr
data LVal =
    VConst Constant
  | VPair LVal LVal
  | VClosure (Map Variable LVal) Variable LType LExpr

data Usage = Z | L | Unknown

class UsageOps tp where
    (+?) :: tp -> tp -> Maybe tp
    (=?) :: tp -> tp -> Maybe tp

instance UsageOps Usage where
    (+?) :: Usage -> Usage -> Maybe Usage
    Z +? u = Just u
    u +? Z = Just u
    L +? L = Nothing
    L +? Unknown = Just L
    Unknown +? L = Just L
    Unknown +? Unknown = Just Unknown

    (=?) :: Usage -> Usage -> Maybe Usage
    Z =? Z = Just Z
    L =? L = Just L
    Unknown =? u = Just u
    u =? Unknown = Just u
    _ =? _ = Nothing

mapM2WithIndex :: forall m key value a. (Ord key, Monad m)
    => (key -> value -> value -> m a) -> Map key value -> Map key value -> m (Map key a)
mapM2WithIndex f m1 m2 = Map.foldrWithKey g (return Map.empty) m1
    where
        g :: key -> value -> m (Map key a) -> m (Map key a)
        g k v1 res = do
            case Map.lookup k m2 of
                Just v2 -> do
                    v <- f k v1 v2;
                    fmap (Map.insert k v) res
                Nothing -> res
instance (Ord key) => UsageOps (Map key Usage) where
    m1 +? m2 = mapM2WithIndex (const (+?)) m1 m2
    m1 =? m2 = mapM2WithIndex (const (=?)) m1 m2

isLinear :: Usage -> Bool
isLinear Z = False
isLinear L = True
isLinear Unknown = True

eqMod :: Int -> Zmod -> Zmod -> Bool
eqMod d x y = (x `mod` d) == (y `mod` d)

assertEq :: (Eq a) => a -> a -> Maybe ()
assertEq x y = if x == y then Just () else Nothing

typecheck :: Map Variable LType -> LExpr -> Maybe (LType, Map Variable Usage)
typecheck delta (Var x) = do
    alpha <- Map.lookup x delta;
    -- gamma : x ↦ L
    --         _ ↦ Z
    let gamma = Map.mapWithKey (\y _ -> if x==y then L else Z) delta
    return (alpha, gamma)

typecheck delta (Zero alpha) = do
    let gamma = Map.map (const Unknown) delta
    return (alpha, gamma)
typecheck delta (Plus a1 a2) = do
    (alpha1, gamma1) <- typecheck delta a1;
    (alpha2, gamma2) <- typecheck delta a2;
    assertEq alpha1 alpha2;
    gamma <- gamma1 =? gamma2;
    return (alpha1, gamma)
typecheck delta (Const r) =
    return (Unit, Map.map (const Z) delta)

typecheck delta (Scale a1 a2) = do
    (alpha1, gamma1) <- typecheck delta a1;
    assertEq alpha1 Unit;
    (alpha2, gamma2) <- typecheck delta a2;
    gamma <- gamma1 +? gamma2;
    return (alpha2, gamma)

typecheck delta (Pair a1 a2) = do
    (alpha1, gamma1) <- typecheck delta a1;
    (alpha2, gamma2) <- typecheck delta a2;
    gamma <- gamma1 =? gamma2;
    return (Sum alpha1 alpha2, gamma)
typecheck delta (Case a x1 a1 x2 a2) = do
    (alpha, gamma) <- typecheck delta a;
    case alpha of
        Sum alpha1 alpha2 -> do
            let delta1 = Map.insert x1 alpha1 delta
                delta2 = Map.insert x2 alpha2 delta
            (alpha1', gamma1) <- typecheck delta1 a1;
            (alpha2', gamma2) <- typecheck delta2 a2;

            assertEq alpha1' alpha2';
            isLinear `fmap` Map.lookup x1 gamma1;
            isLinear `fmap` Map.lookup x2 gamma2;

            gamma' <- Map.delete x1 gamma1 =? Map.delete x2 gamma2;
            gamma'' <- gamma1 +? gamma';
            return (alpha1', gamma'')
        _ -> Nothing
    
typecheck delta (Lambda x alpha1 a) = do
    (alpha2, gamma) <- typecheck (Map.insert x alpha1 delta) a;
    return (Arrow alpha1 alpha2, gamma)
typecheck delta (Apply a1 a2) = do
    (alpha1, gamma1) <- typecheck delta a1;
    (alpha2, gamma2) <- typecheck delta a2;
    gamma <- gamma1 +? gamma2;
    case alpha1 of
        Arrow alpha alpha' -> assertEq alpha alpha2 >> return (alpha', gamma)
        _ -> Nothing

-- EvalMonad should include:
--      fresh
--      error

type EvalMonad = StateT Variable Maybe
fresh :: EvalMonad Variable
fresh = do
    x <- get;
    put (x + 1);
    return x

vZero :: LType -> EvalMonad LVal
vZero Unit = return $ VConst 0
vZero (Sum alpha1 alpha2) = do
    v1 <- vZero alpha1;
    v2 <- vZero alpha2;
    return (VPair v1 v2)
vZero (Arrow alpha1 alpha2) = do
    x <- fresh;
    return (VClosure Map.empty x alpha1 (Zero alpha2))

rename :: Variable -> Variable -> LExpr -> LExpr
rename = undefined

vPlus :: LVal -> LVal -> EvalMonad LVal
vPlus (VConst r1) (VConst r2) = return (VConst $ r1 + r2)
vPlus (VPair v11 v12) (VPair v21 v22) = do
    v1 <- vPlus v11 v21;
    v2 <- vPlus v12 v22;
    return (VPair v1 v2)
vPlus (VClosure ctx1 x1 alpha1 a1) (VClosure ctx2 x2 _ a2) = do
    x <- fresh;
    ctx <- mapM2WithIndex (const vPlus) ctx1 ctx2
    return $ VClosure ctx x alpha1 (Plus (rename x1 x a1) (rename x2 x a2))
vPlus _ _ = throwError ()

vScale :: LVal -> LVal -> EvalMonad LVal
vScale (VConst r) (VConst r') = return . VConst $ r * r'
vScale v (VPair v1 v2) = do
    v1' <- vScale v v1;
    v2' <- vScale v v2;
    return $ VPair v1' v2'
vScale (VConst r) (VClosure ctx x tp a) = 
    return $ VClosure ctx x tp (Scale (Const r) a)
vScale _ _ = throwError ()

eval :: Map Variable LVal -> LExpr -> EvalMonad LVal
eval ctx (Var x) = case Map.lookup x ctx of
    Just v -> return v
    Nothing -> throwError ()
eval ctx (Zero alpha) = vZero alpha
eval ctx (Plus a1 a2) = do
    v1 <- eval ctx a1;
    v2 <- eval ctx a2;
    vPlus v1 v2
eval ctx (Const r) = return $ VConst r
eval ctx (Scale a1 a2) = do
    v1 <- eval ctx a1;
    v2 <- eval ctx a2;
    vScale v1 v2
eval ctx (Pair a1 a2) = do
    v1 <- eval ctx a1;
    v2 <- eval ctx a2;
    return (VPair v1 v2)
eval ctx (Case a x1 a1 x2 a2) = eval ctx a >>= \case
    VPair v1 v2 -> do
        let ctx1 = Map.insert x1 v1 ctx
            ctx2 = Map.insert x2 v2 ctx
        v1 <- eval ctx1 a1;
        v2 <- eval ctx2 a2;
        vPlus v1 v2
    _ -> throwError ()
eval ctx (Lambda x alpha a) = return $ VClosure ctx x alpha a
eval ctx (Apply a1 a2) = eval ctx a1 >>= \case
    VClosure ctx' x _ a -> do
        v <- eval ctx a2;
        -- note that the domains of ctx and ctx' should be disjoint
        eval (Map.union ctx' (Map.insert x v ctx)) a
    _ -> throwError ()

main = do putStrLn "Hello, world!";
          print (eqMod 3 4 7);
          print (eqMod 3 4 8)