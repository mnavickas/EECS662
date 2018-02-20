{-# LANGUAGE GADTs, FlexibleContexts #-}
--
-- Author: Michael Navickas
-- ID: 2762570
-- Date: 2/19/2018

-- Imports for Parsec
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

-- AST Definition

data TABE where
  TNum :: TABE
  TBool :: TABE
  deriving (Show,Eq)

data ABE where
  Num :: Int -> ABE
  Plus :: ABE -> ABE -> ABE
  Minus :: ABE -> ABE -> ABE
  Mult :: ABE -> ABE -> ABE
  Div :: ABE -> ABE -> ABE
  Boolean :: Bool -> ABE
  And :: ABE -> ABE -> ABE
  Leq :: ABE -> ABE -> ABE
  IsZero :: ABE -> ABE
  If :: ABE -> ABE -> ABE -> ABE
  deriving (Show,Eq)

-- AST Pretty Printer
pprint :: ABE -> String
pprint (Num n) = show n
pprint (Boolean b) = show b
pprint (Plus n m) = "(" ++ pprint n ++ " + " ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ " - " ++ pprint m ++ ")"
pprint (Mult n m) = "(" ++ pprint n ++ " * " ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ " / " ++ pprint m ++ ")"
pprint (And n m) = "(" ++ pprint n ++ " && " ++ pprint m ++ ")"
pprint (Leq n m) = "(" ++ pprint n ++ " <= " ++ pprint m ++ ")"
pprint (IsZero m) = "(0 == " ++ pprint m ++ ")"
pprint (If c n m) = "(if " ++ pprint c ++ " then " ++ pprint n ++ " else " ++ pprint m ++ ")"

-- Parser (Requires ParserUtils and Parsec)
languageDef =
  javaStyle { identStart = letter
            , identLetter = alphaNum
            , reservedNames = [ "if0"
                              , "then"
                              , "else"
                              ]
            , reservedOpNames = [ "+","-","*","/"]
            }
  
lexer = makeTokenParser languageDef

inFix o c a = (Infix (reservedOp lexer o >> return c) a)
preFix o c = (Prefix (reservedOp lexer o >> return c))
postFix o c = (Postfix (reservedOp lexer o >> return c))

parseString p str =
  case parse p "" str of
    Left e -> error $ show e
    Right r -> r

expr :: Parser ABE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "*" Mult AssocLeft
            , inFix "/" Div AssocLeft ]
          , [ inFix "+" Plus AssocLeft
            , inFix "-" Minus AssocLeft ]
          , [ inFix "<=" Leq AssocLeft
            , preFix "isZero" IsZero ]
          , [ inFix "&&" And AssocLeft ]
          ]

numExpr :: Parser ABE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

trueExpr :: Parser ABE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser ABE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser ABE
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)

term = parens lexer expr
       <|> numExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr

-- Parser invocation

parseABE = parseString expr

-- Evaluation Functions
liftNum :: (Int -> Int -> Int) -> ABE -> ABE -> ABE
liftNum f (Num l) (Num r) = (Num (f l r))

liftBool :: (Bool -> Bool -> Bool) -> ABE -> ABE -> ABE
liftBool f (Boolean l) (Boolean r) = (Boolean (f l r))

liftNumBool :: (Int -> Int -> Bool) -> ABE -> ABE -> ABE
liftNumBool f (Num l) (Num r) = (Boolean (f l r))

--Exercise 1 part 1
evalM :: ABE -> (Maybe ABE)
evalM (Num x) = Just (Num x)
evalM (Boolean x) = Just (Boolean x)
evalM (Plus l r) = do   { 
                            l' <- (evalM l);
                            r' <- (evalM r);
                            return (liftNum (+) l' r') 
                        }         
evalM (Minus l r) = do  { 
                            l' <- (evalM l);
                            r' <- (evalM r);
                            case l' of
                            (Num v1) -> case r' of
                                        (Num v2) -> (if v1-v2 >= 0 then return (Num (v1-v2)) else Nothing)
                                        _ -> Nothing
                            _ -> Nothing
                        }
evalM (Mult l r) = do   { 
                            l' <- (evalM l);
                            r' <- (evalM r);
                            return (liftNum (*) l' r') 
                        }
evalM (Div l r) = do    { 
                            l' <- (evalM l);
                            r' <- (evalM r);
                            if r' == Num 0 then Nothing else return (liftNum (div) l' r') 
                        }
evalM (And l r) = do    { 
                            l' <- (evalM l);
                            r' <- (evalM r);
                            return (liftBool (&&) l' r') 
                        }
evalM (Leq l r) = do    { 
                            l' <- (evalM l);
                            r' <- (evalM r);
                            return (liftNumBool (<=) l' r') 
                        }
evalM (IsZero x) = do   {
                            v <- (evalM x);
                            return (Boolean (v == (Num 0)))
                        }
evalM (If c t f) = do   {
                            v <- (evalM c);
                            (if (v==(Boolean True)) then (evalM t) else (evalM f))
                        }

--Exercise 1 part 2
evalErr :: ABE -> (Maybe ABE)
evalErr (Num x) = Just (Num x)
evalErr (Boolean x) = Just (Boolean x)
evalErr (Plus l r) =
  do r1 <- (evalErr l)
     r2 <- (evalErr r)
     case r1 of
       (Num v1) -> case r2 of
                     (Num v2) -> (return (Num (v1+v2)))
                     _ -> Nothing
evalErr (Minus l r) =
  do r1 <- (evalErr l)
     r2 <- (evalErr r)
     case r1 of
       (Num v1) -> case r2 of
                     (Num v2) -> if v1-v2 >= 0 then (return (Num (v1-v2))) else Nothing
                     _ -> Nothing
evalErr (Mult l r) =
  do r1 <- (evalErr l)
     r2 <- (evalErr r)
     case r1 of
       (Num v1) -> case r2 of
                     (Num v2) -> (return (Num (v1*v2)))
                     _ -> Nothing
evalErr (Div l r) =
  do r1 <- (evalErr l)
     r2 <- (evalErr r)
     case r1 of
       (Num v1) -> case r2 of
                     (Num v2) -> if v2 == 0 then Nothing else (return (Num (div v1 v2)))
                     _ -> Nothing
evalErr (And l r) =
  do r1 <- (evalErr l)
     r2 <- (evalErr r)
     case r1 of
       (Boolean v1) -> case r2 of
                         (Boolean v2) -> (return (Boolean (v1 && v2)))
                         _ -> Nothing
       _ -> Nothing
evalErr (Leq l r) = 
  do r1 <- (evalErr l)
     r2 <- (evalErr r)
     case r1 of
       (Num v1) -> case r2 of
                     (Num v2) -> (return (Boolean (v1 <= v2)))
                     _ -> Nothing
       _ -> Nothing
evalErr (IsZero t) =
  do r <- (evalErr t)
     case r of
       (Num v) -> (return (Boolean (v == 0)))
       _ -> Nothing
evalErr (If c t f) =
  do r <- (evalErr c)
     case r of
       (Boolean v) -> if v then (evalErr t) else (evalErr f)
       _ -> Nothing

--Exercise 1 part 3
-- Type Derivation Function
typeofM :: ABE -> Maybe TABE
typeofM (Num _) =   return TNum
typeofM (Plus l r) = do     {
                                l' <- (typeofM l);
                                r' <- (typeofM r);
                                if l'==TNum && r'==TNum then return TNum else Nothing
                            }
typeofM (Minus l r) = do    {
                                l' <- (typeofM l);
                                r' <- (typeofM r);
                                if l'==TNum && r'==TNum then return TNum else Nothing
                            }
typeofM (Div l r) = do      {
                                l' <- (typeofM l);
                                r' <- (typeofM r);
                                if l'==TNum && r'==TNum then return TNum else Nothing
                            }
typeofM (Mult l r) = do     {
                                l' <- (typeofM l);
                                r' <- (typeofM r);
                                if l'==TNum && r'==TNum then return TNum else Nothing
                            }
typeofM (Boolean _) =   return TBool
typeofM (And l r) = do  {
                            l' <- (typeofM l);
                            r' <- (typeofM r);
                            if l'==TBool && r'==TBool then (return TBool) else Nothing
                        }
typeofM (Leq l r) = do  {
                            l' <- (typeofM l);
                            r' <- (typeofM r);
                            if l'==TNum && r'==TNum then (return TBool) else Nothing
                        }
typeofM (IsZero t) = do {   
                            t' <- (typeofM t);
                            if t'==TNum then (return TBool) else Nothing
                        }
typeofM (If c t e) = do {
                            c' <- (typeofM c);
                            t' <- (typeofM t);
                            e' <- (typeofM e);
                            if c' == TBool && t'== e' then (return t') else Nothing
                        }

-- Optimizer
optimize :: ABE -> ABE
optimize (Num a) = Num a
optimize (Boolean a) = Boolean a
optimize (Mult l r) = Mult (optimize l) (optimize r)
optimize (Div l r) = Div (optimize l) (optimize r)
optimize (Minus l r) = Minus (optimize l) (optimize r)
optimize (Leq l r) = Leq (optimize l) (optimize r)
optimize (IsZero c) = IsZero (optimize c)
optimize (And l r) = And (optimize l) (optimize r)
optimize (If c t f)
    | (c' == Boolean True) = t'
    | (c' == Boolean False) = f'
    | otherwise = If c' t' f'
    where   c' = optimize c
            t' = optimize t
            f' = optimize f
optimize (Plus l r)
    | (l' == Num 0) = r'
    | (r' == Num 0) = l'
    | otherwise = Plus l' r'
    where   l' = optimize l
            r' = optimize r

--Exercise part 2
interpOptM :: ABE -> Maybe ABE
interpOptM = evalM . optimize

--Exercise 1 part 4
-- Combined interpreter
evalTypeM :: ABE -> Maybe ABE
evalTypeM a = do    {
                    typeofM a;
                    evalM a;
                    }

evalTypeOptM :: ABE -> Maybe ABE
evalTypeOptM a = do    {
                    typeofM a;
                    evalM $ optimize a;
                    }


testCases = [    "(if true && isZero 1 then 5 else 6)+0+0+0+0"
                ,"(5+5-3) + if (isZero 5+5) then (5-4) else (5*8)"
                , "if 1 <= (6/4) then true && true else false && true"
                , "true && 5 <= 6 && true"
                , "true && 7 <= 6 && true"
                , "5+5"
                , "5-4"
                , "15/3"
                , "3*5"
                , "if true then 1 else 0"
                , "0 <= 1"
                , "true && false" ]

runTests = do
    putStrLn $ "Pre optimize"
    putStrLn $ unlines $ map pprint parsed
    putStrLn $ "Post optimize"   
    putStrLn $ unlines $ map pprint (map optimize parsed )
    putStrLn $ "\nEvals"
    putStrLn $ show $ map evalM parsed
    putStrLn $ show $ map evalErr parsed
    putStrLn $ show $ map evalTypeM parsed
    putStrLn $ show $ map interpOptM parsed
    putStrLn $ show $ map evalTypeOptM parsed
        where parsed = (map parseABE  testCases) 

main = runTests