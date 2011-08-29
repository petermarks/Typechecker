{-# OPTIONS -fglasgow-exts #-}

-- Typechecker to GADT
-- Implementing a typed DSL with the typed evaluator and the 
-- the typechecker from untyped terms to typed ones

module TypecheckedDSL where

-- Untyped terms (what I get from my parser):

data Exp 
  = EDouble     Double
  | EString     String
	| EIdentifier String
	| EApp        Exp Exp
	deriving (Show)

-- Typed terms:

data Term :: * -> * where
  Prim :: Primitive a -> Term a
  App  :: Term (a->b) -> Term a -> Term b


-- Primitives

data Primitive :: * -> * where
  Num  :: Double -> Primitive Double
  Str  :: String -> Primitive String
  Rev  :: Primitive (String -> String)
  Show :: Primitive (Double -> String)
  Inc  :: Primitive (Double -> Double)
  Plus :: Primitive (Double -> Double -> Double)


-- Typed evaluator

eval :: Term a -> a
eval (Prim x) = evalPrim x
eval (App e1 e2) = (eval e1) (eval e2)

evalPrim :: Primitive a -> a
evalPrim (Num x) = x
evalPrim (Str x) = x
evalPrim Rev     = reverse
evalPrim Show    = show
evalPrim Inc     = (+ 1)
evalPrim Plus    = (+)


-- Types and type comparison

data Typ a where
    TDouble :: Typ Double
    TString :: Typ String
    TFun    :: Typ a -> Typ b -> Typ (a->b)

data EQ a b where
    Refl :: EQ a a

-- checking that two types are the same. If so, give the witness

eqt :: Typ a -> Typ b -> Maybe (EQ a b)
eqt TDouble TDouble = Just $ Refl
eqt TString TString = Just $ Refl
eqt (TFun ta1 tb1) (TFun ta2 tb2) = eqt' (eqt ta1 ta2) (eqt tb1 tb2)
 where
   eqt' :: (Maybe (EQ ta1 ta2)) -> Maybe (EQ tb1 tb2) -> 
	   Maybe (EQ (ta1 -> tb1) (ta2 -> tb2))
   eqt' (Just Refl) (Just Refl) = Just Refl
   eqt' _ _ = Nothing
eqt _ _ = Nothing

instance Show (Typ a) where
    show TDouble = "Double"
    show TString = "String"
    show (TFun ta tb) = "(" ++ show ta ++ "->" ++ show tb ++ ")"
    
class    Typed a      where typ :: Typ a
instance Typed Double where typ = TDouble
instance Typed String where typ = TString
instance (Typed a, Typed b) => Typed (a -> b) where typ = TFun typ typ


-- Type checking
data TypedTerm = forall t. TypedTerm (Typ t) (Term t)

-- Typing environment
type Gamma = [(String,TypedTerm)]


-- Initial environment (the types of primitives)

env0 =
  [ ("rev",  tt Rev)
  , ("show", tt Show)
  , ("inc",  tt Inc)
  , ("+",    tt Plus)
  ]

tt t = TypedTerm typ (Prim t)

typecheck :: Gamma -> Exp -> Either String TypedTerm
typecheck _ (EDouble x) = Right $ tt (Num x)
typecheck _ (EString x) = Right $ tt (Str x)
typecheck env (EIdentifier x) = maybe err Right $ lookup x env
  where err = Left $ "unknown identifier: " ++ x
typecheck env (EApp e1 e2) =
  case (typecheck env e1, typecheck env e2) of
    (Right e1, Right e2) -> typechecka e1 e2
    (Left err, Right _)  -> Left err
    (Right _,  Left err) -> Left err
    (Left e1,  Left e2) ->  Left (e1 ++ " and " ++ e2)


-- typecheck the application
-- Because of the new implementation of GADT pattern matching
-- in GHC 6.10, the signature is now required.
-- Kindly pointed out by Marcin Zalewski.
typechecka :: TypedTerm -> TypedTerm -> Either String TypedTerm
typechecka (TypedTerm (TFun ta tb) e1) (TypedTerm t2 e2) =
  typechecka' (eqt ta t2) tb e1 e2
 where
  typechecka' :: Maybe (EQ ta t2) -> Typ tb -> Term (ta->tb) -> Term t2 ->
		 Either String TypedTerm
  typechecka' (Just Refl) tb e1 e2 = Right $ TypedTerm tb (App e1 e2)
  typechecka' _ tb e1 e2 = 
     Left $ unwords ["incompatible type of the application:",
		     show (TFun ta tb), "and", show t2]

typechecka (TypedTerm t1 e1) _ = 
    Left $ "Trying to apply not-a-function: " ++ show t1



-- tests

te1 = EApp (EIdentifier "inc") (EDouble 10.0)
te2 = EApp (EDouble 10.0) (EIdentifier "inc")
te3 = EApp (EApp (EIdentifier "+") 
	     (EApp (EIdentifier "inc") (EDouble 10.0)))
           (EApp (EIdentifier "inc") (EDouble 20.0))
            
te4 = EApp (EIdentifier "rev") te3
te5 = EApp (EIdentifier "rev") (EApp (EIdentifier "show") te3)


-- typecheck-and-eval

teval :: Exp  -> String
teval exp = either (terror) (ev) (typecheck env0 exp)
 where
  terror err = "Type error: " ++ err
  ev (TypedTerm t e) = "type " ++ show t ++ ", value " ++
       (tryshow (eqt t TString) (eqt t TDouble) (eval e))
  tryshow :: Maybe (EQ t String) -> Maybe (EQ t Double) -> t -> String
  tryshow (Just Refl) _ t = t
  tryshow _ (Just Refl) t = show t
  tryshow _ _ _ = "<fun>"

{-
*TypecheckedDSL> teval te1
"type Double, value 11.0"

*TypecheckedDSL> teval te2
"Type error: Trying to apply not-a-function: Double"

*TypecheckedDSL> teval te3
"type Double, value 32.0"

*TypecheckedDSL> teval te4
"Type error: incompatible type of the application: (String->String) and Double"

*TypecheckedDSL> teval te5
"type String, value 0.23"
-}
