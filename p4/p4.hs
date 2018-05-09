{-# LANGUAGE GADTs #-}

import Text.ParserCombinators.Parsec
import Control.Monad
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as Token

-- Calculator language extended with an environment to hold defined variables

data TFBAE where
  TNum :: TFBAE
  TBool :: TFBAE
  (:->:) :: TFBAE -> TFBAE -> TFBAE
  deriving (Show,Eq)

data FBAE where
  Num :: Int -> FBAE
  Plus :: FBAE -> FBAE -> FBAE
  Minus :: FBAE -> FBAE -> FBAE
  Mult :: FBAE -> FBAE -> FBAE
  Div :: FBAE -> FBAE -> FBAE
  Bind :: String -> FBAE -> FBAE -> FBAE
  Lambda :: String -> TFBAE -> FBAE -> FBAE
  App :: FBAE -> FBAE -> FBAE
  Id :: String -> FBAE
  Boolean :: Bool -> FBAE
  And :: FBAE -> FBAE -> FBAE
  Or :: FBAE -> FBAE -> FBAE
  Leq :: FBAE -> FBAE -> FBAE
  IsZero :: FBAE -> FBAE
  If :: FBAE -> FBAE -> FBAE -> FBAE
  Fix :: FBAE -> FBAE
  deriving (Show,Eq)

-- Value defintion for statically scoped eval

data FBAEVal where
  NumV :: Int -> FBAEVal
  BooleanV :: Bool -> FBAEVal
  ClosureV :: String -> TFBAE -> FBAE -> Env -> FBAEVal
  deriving (Show,Eq)

-- Environment for statically scoped eval

type Env = [(String,FBAEVal)]
subst :: String -> FBAE -> FBAE -> FBAE
subst _ _ (Num x) = (Num x)
subst _ _ (Boolean x) = (Boolean x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Mult l r) = (Mult (subst i v l) (subst i v r))
subst i v (Div l r) = (Div (subst i v l) (subst i v r))
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Or l r) = (Or (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero x) = (IsZero (subst i v x))
subst i v (If c t f) = (If (subst i v c) (subst i v t) (subst i v f))
subst i v (Lambda i' t' b') = (Lambda i' t' (subst i v b'))
subst i v (App f' a') = (App (subst i v f') (subst i v a') )
subst i v (Fix f) = Fix (subst i v f)
subst i v (Bind i' v' b') = if i==i'
                            then (Bind i' (subst i v v') b')
                            else (Bind i' (subst i v v') (subst i v b'))
subst i v (Id i') = if i==i'
                    then v
                    else (Id i')

-- Statically scoped eval
evalM :: Env -> FBAE -> (Maybe FBAEVal)
evalM e (Num x) = Just (NumV x)
evalM e (Boolean x) = Just (BooleanV x)
evalM e (Plus l r) = do   {
                            NumV l' <- (evalM e l);
                            NumV r' <- (evalM e r);
                            return( NumV (l' + r') )
                          }
evalM e (Minus l r) = do  {
                            NumV l' <- (evalM e l);
                            NumV r' <- (evalM e r);
                            return( NumV (l' - r') )
                          }
evalM e (Mult l r) = do   {
                            NumV l' <- (evalM e l);
                            NumV r' <- (evalM e r);
                            return( NumV (l' * r') )
                          }
evalM e (Div l r) = do    {
                            NumV l' <- (evalM e l);
                            NumV r' <- (evalM e r);
                            if r' /= 0 then return( NumV (l' `div` r') ) else Nothing
                          }
evalM e (Bind i v b) = do {
                            v' <- (evalM e v);
                            evalM ((i,v'):e) b
                          }
evalM e (Lambda i t b) =  return (ClosureV i t b e)   
evalM e (App f a) = do    {
                              a' <- evalM e a;
                              (ClosureV i t b e') <- evalM e f;
                              evalM ((i,a'):e') b
                          }
evalM e (Id i) =          lookup i e
evalM e (And l r) = do    {
                            BooleanV l' <- (evalM e l);
                            BooleanV r' <- (evalM e r);
                            return( BooleanV (l' && r') )
                          }
evalM e (Or l r) = do     {
                            BooleanV l' <- (evalM e l);
                            BooleanV r' <- (evalM e r);
                            return( BooleanV (l' || r') )
                          }
evalM e (Leq l r) = do    {
                            NumV l' <- (evalM e l);
                            NumV r' <- (evalM e r);
                            return( BooleanV (l' <= r') )
                          }
evalM e (IsZero l) = do   {
                            NumV l' <- (evalM e l);
                            return( BooleanV (l' == 0) )
                          }
evalM e (If c t f) = do   {
                            BooleanV v <- (evalM e c);
                            if v then (evalM e t) else (evalM e f)
                          }
evalM e (Fix f) = do      {
                            (ClosureV i' t' b' e') <- evalM e f;
                            evalM e' (subst i' (Fix (Lambda i' t' b')) b')
                          }                          



-- Type inference function

type Cont = [(String,TFBAE)]

typeofM :: Cont -> FBAE -> (Maybe TFBAE)
typeofM _ (Num _) = Just TNum
typeofM _ (Boolean _) = Just TBool
typeofM c (Plus l r) = do   {
                            l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l' == TNum && r' == TNum then
                              return TNum
                              else Nothing
                            }
typeofM c (Minus l r) = do  {
                            l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l' == TNum && r' == TNum then
                              return TNum
                              else Nothing
                            }
typeofM c (Mult l r) = do  {
                            l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l' == TNum && r' == TNum then
                              return TNum
                              else Nothing
                            }
typeofM c (Div l r) = do    {
                            l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l' == TNum && r' == TNum then
                              return TNum
                              else Nothing
                            }
typeofM c (And l r) = do    {
                            l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l' == TBool && r' == TBool then
                              return TBool
                              else Nothing
                            }
typeofM c (Or l r) = do    {
                            l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l' == TBool && r' == TBool then
                              return TBool
                              else Nothing
                            }
typeofM c (Leq l r) = do    {
                            l' <- (typeofM c l);
                            r' <- (typeofM c r);
                            if l' == TNum && r' == TNum then
                              return TBool
                              else Nothing
                            }
typeofM c (IsZero x) = do   {
                            x' <- (typeofM c x);
                            if x' == TNum then
                              return TBool
                              else Nothing
                            }
typeofM cx (If c t f) = do   do {
                            c' <- (typeofM cx c);
                            t' <- (typeofM cx t);
                            f' <- (typeofM cx f);
                            if c' == TBool && t'== f' then
                              return t'
                              else Nothing
                        }
typeofM c (Bind i v b) = do {
                            v' <- (typeofM c v) ;
                            typeofM ((i,v'):c) b
                            }
typeofM c (Id i) = lookup i c
typeofM c (App f a) = do    {
                              a' <- typeofM c a;
                              (d:->:r) <- typeofM c f;
                              if d == a' then
                                return r
                              else
                                Nothing
                            }
typeofM c (Lambda i t b) = do {
                                r <- typeofM ((i,t):c) b;
                                return (t:->:r)
                              }
typeofM c (Fix f) = do  {
                          (d:->:r) <- typeofM c f;
                          return r
                        }

-- Interpreter

interp :: FBAE -> (Maybe FBAEVal)
interp f = let env = [] in
              do  {  
                    typeofM env f;
                    evalM env f
                  }

-- Factorial function for testing evalM and typeofM.  the type of test1 should
-- be TNum and the result of evaluating test1`should be (NumV 6).  Remember
-- that Just is used to return both the value and type.

testCases = [

          (Bind "f" (Lambda "g" ((:->:) TNum TNum)
                    (Lambda "x" TNum (If (IsZero (Id "x")) (Num 1)
                                         (Mult (Id "x")
                                               (App (Id "g")
                                                    (Minus (Id "x")
                                                           (Num 1)))))))
          (App (Fix (Id "f")) (Num 3)))

          ,

    
          (Bind "x" (Num 5)
                  (Bind "func" (Lambda "arg" TNum (Plus (Id "arg") (Id "x"))) 
                      (Bind "x" (Num 0) 
                          (App (Id "func") (Num 10))
                      )
                  )
              )
          ]
runTests = putStrLn $ show $ map interp testCases

