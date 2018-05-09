{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- CFAE AST and Type Definitions

data CFAE where
  Num :: Int -> CFAE
  Plus :: CFAE -> CFAE -> CFAE
  Minus :: CFAE -> CFAE -> CFAE
  Mult :: CFAE -> CFAE -> CFAE
  Lambda :: String -> CFAE -> CFAE
  App :: CFAE -> CFAE -> CFAE
  Id :: String -> CFAE
  If0 :: CFAE -> CFAE -> CFAE -> CFAE
  deriving (Show,Eq)

type Env = [(String,CFAE)]

evalDynCFAE :: Env -> CFAE -> (Maybe CFAE)
evalDynCFAE e (Num x) = Just (Num x)
evalDynCFAE e (Plus l r) = do   {
                            Num l' <- (evalDynCFAE e l);
                            Num r' <- (evalDynCFAE e r);
                            return( Num (l' + r') )
                        }
evalDynCFAE e (Minus l r) = do  {
                            Num l' <- (evalDynCFAE e l);
                            Num r' <- (evalDynCFAE e r);
                            return( Num (l' - r') )
                        }
evalDynCFAE e (Mult l r) = do  {
                            Num l' <- (evalDynCFAE e l);
                            Num r' <- (evalDynCFAE e r);
                            return( Num (l' * r') )
                        }
evalDynCFAE e (If0 c t f) = do   {
                            Num v <- (evalDynCFAE e c);
                            if (v==0) then (evalDynCFAE e t) else (evalDynCFAE e f)
                        }
evalDynCFAE e (App f a) = do {
                          a' <- evalDynCFAE e a;
                          (Lambda i b) <- evalDynCFAE e f;
                          evalDynCFAE ((i,a'):e) b
                        }
evalDynCFAE e (Lambda i b) = return (Lambda i b) 
evalDynCFAE e (Id i) = lookup i e


data CFAEValue where
  NumV :: Int -> CFAEValue
  ClosureV :: String -> CFAE -> Env' -> CFAEValue
  deriving (Show,Eq)

type Env' = [(String,CFAEValue)]

evalStatCFAE :: Env' -> CFAE -> (Maybe CFAEValue)
evalStatCFAE e (Num x) = Just (NumV x)
evalStatCFAE e (Plus l r) = do   {
                            NumV l' <- (evalStatCFAE e l);
                            NumV r' <- (evalStatCFAE e r);
                            return( NumV (l' + r') )
                        }
evalStatCFAE e (Minus l r) = do  {
                            NumV l' <- (evalStatCFAE e l);
                            NumV r' <- (evalStatCFAE e r);
                            return( NumV (l' - r') )
                        }
evalStatCFAE e (Mult l r) = do  {
                            NumV l' <- (evalStatCFAE e l);
                            NumV r' <- (evalStatCFAE e r);
                            return( NumV (l' * r') )
                        }
evalStatCFAE e (If0 c t f) = do   {
                            NumV v <- (evalStatCFAE e c);
                            if (v==0) then (evalStatCFAE e t) else (evalStatCFAE e f)
                        }
evalStatCFAE e (Lambda i b) = return (ClosureV i b e) 
evalStatCFAE e (Id i) = lookup i e
evalStatCFAE e (App f a) = do {
                              a' <- evalStatCFAE e a;
                              (ClosureV i b e') <- evalStatCFAE e f;
                              evalStatCFAE ((i,a'):e') b
                            }

data CFBAE where
  Num' :: Int -> CFBAE
  Plus' :: CFBAE -> CFBAE -> CFBAE
  Minus' :: CFBAE -> CFBAE -> CFBAE
  Mult' :: CFBAE -> CFBAE -> CFBAE
  Lambda' :: String -> CFBAE -> CFBAE
  App' :: CFBAE -> CFBAE -> CFBAE
  Bind' :: String -> CFBAE -> CFBAE -> CFBAE
  Id' :: String -> CFBAE
  If0' :: CFBAE -> CFBAE -> CFBAE -> CFBAE
  deriving (Show,Eq)

elabCFBAE :: CFBAE -> CFAE
elabCFBAE (Num' a) = Num a
elabCFBAE (Plus' a b)= Plus (elabCFBAE a) (elabCFBAE b)
elabCFBAE (Minus' a b)= Minus (elabCFBAE a) (elabCFBAE b)
elabCFBAE (Mult' a b)= Mult (elabCFBAE a) (elabCFBAE b)
elabCFBAE (Lambda' i b)= Lambda i (elabCFBAE b)
elabCFBAE (App' l v)= App (elabCFBAE l) (elabCFBAE v)
elabCFBAE (Bind' i v b)= App (Lambda i (elabCFBAE b)) (elabCFBAE v)
elabCFBAE (Id' a) = Id a
elabCFBAE (If0' a b c)= If0 (elabCFBAE a) (elabCFBAE b) (elabCFBAE c)


evalCFBAE :: Env' -> CFBAE -> (Maybe CFAEValue)
evalCFBAE env expr = evalStatCFAE env $ elabCFBAE expr

evalDynCFBAE :: Env -> CFBAE -> (Maybe CFAE)
evalDynCFBAE env expr = evalDynCFAE env $ elabCFBAE expr



expressions =   [     
                    (Bind' "x" (Num' 5)
                        (Bind' "func" (Lambda' "arg" (Plus' (Id' "arg") (Id' "x"))) 
                            (Bind' "x" (Num' 0) 
                                (App' (Id' "func") (Num' 10))
                            )
                        )
                    )
-- Bind x = 5 in
    -- Bind func = (Lambda arg = arg+x) in
        -- Bind x = 0 in
            -- app func 10

                ,
                    (Bind' "x" (Num' 5)
                        (Bind' "func" (Lambda' "arg" (Plus' (Id' "x") (Id' "x"))) 
                            (Bind' "x" (Num' 0) 
                                (App' (Id' "func") (Num' 10))
                            )
                        )
                    )
-- Bind x = 5 in
    -- Bind func = (Lambda arg = x+x) in
        -- Bind x = 0 in
            -- app func 10

                ,
                    (Bind' "fact" (Lambda' "n" (If0' (Id' "n") (Num' 1) ( Mult' (Id' "n") (App' (Id' "fact") (Minus' (Id' "n") (Num' 1) )))))
                        (App' (Id' "fact") (Num' 5))
                        
                    )
--static scope will fail this
-- Bind fact = <factorial func> in
    -- app fact 5

                ]
runTests = 
    do  putStrLn $ show $ map (evalCFBAE []) expressions
        putStrLn $ show $ map (evalDynCFBAE []) expressions

main = runTests
                                                    
                                                    




