{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

data TBBAE where
  TNum :: TBBAE
  TBool :: TBBAE
  deriving (Show,Eq)

data BBAE where
  Num :: Int -> BBAE
  Plus :: BBAE -> BBAE -> BBAE
  Minus :: BBAE -> BBAE -> BBAE
  Bind :: String -> BBAE -> BBAE -> BBAE
  Id :: String -> BBAE
  Boolean :: Bool -> BBAE
  And :: BBAE -> BBAE -> BBAE
  Leq :: BBAE -> BBAE -> BBAE
  IsZero :: BBAE -> BBAE
  If :: BBAE -> BBAE -> BBAE -> BBAE
  deriving (Show,Eq)

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

expr :: Parser BBAE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "+" Plus AssocLeft
            , inFix "-" Minus AssocLeft ]
          , [ inFix "<=" Leq AssocLeft
            , preFix "isZero" IsZero ]
          , [ inFix "&&" And AssocLeft ]
          ]

numExpr :: Parser BBAE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

trueExpr :: Parser BBAE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser BBAE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser BBAE
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)

bindExpr :: Parser BBAE
bindExpr = do reserved lexer "bind"
              i <- identifier lexer
              reservedOp lexer "="
              v <- expr
              reserved lexer "in"
              e <- expr
              return (Bind i v e)

identExpr :: Parser BBAE
identExpr = do i <- identifier lexer
               return (Id i)

term = parens lexer expr
       <|> numExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr
       <|> bindExpr
       <|> identExpr


-- BBAE AST and Type Definitions

type Env = [(String,BBAE)]

type Cont = [(String,TBBAE)]

subst :: String -> BBAE -> BBAE -> BBAE
subst _ _ (Num x) = (Num x)
subst _ _ (Boolean x) = (Boolean x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero x) = (IsZero (subst i v x))
subst i v (If c t f) = (If (subst i v c) (subst i v t) (subst i v f))
subst i v (Bind i' v' b') = if i==i'
                            then (Bind i' (subst i v v') b')
                            else (Bind i' (subst i v v') (subst i v b'))
subst i v (Id i') = if i==i'
                    then v
                    else (Id i')

evalS :: BBAE -> (Maybe BBAE)
evalS (Num x) = Just (Num x)
evalS (Boolean x) = Just (Boolean x)
evalS (Plus l r) = do   {
                            Num l' <- (evalS l);
                            Num r' <- (evalS r);
                            return( Num (l' + r') )
                        }
evalS (Minus l r) = do  {
                            Num l' <- (evalS l);
                            Num r' <- (evalS r);
                            return( Num (l' - r') )
                        }
evalS (And l r) = do    {
                            Boolean l' <- (evalS l);
                            Boolean r' <- (evalS r);
                            return( Boolean (l' && r') )
                        }
evalS (Leq l r) = do    {
                            Num l' <- (evalS l);
                            Num r' <- (evalS r);
                            return( Boolean (l' <= r') )
                        }
evalS (IsZero x) = do   {
                            Num v <- (evalS x);
                            return( Boolean (v == 0) )
                        }
evalS (If c t f) = do   {
                            Boolean v <- (evalS c);
                            if (v==True) then (evalS t) else (evalS f)
                        }
evalS (Bind i v b) = do {
                          v' <- (evalS v) ;
                          evalS (subst i v' b)
                        }
evalS (Id _) = Nothing


evalM :: Env -> BBAE -> (Maybe BBAE)
evalM e (Num x) = Just (Num x)
evalM e (Boolean x) = Just (Boolean x)
evalM e (Plus l r) = do   {
                            Num l' <- (evalM e l);
                            Num r' <- (evalM e r);
                            return( Num (l' + r') )
                        }
evalM e (Minus l r) = do  {
                            Num l' <- (evalM e l);
                            Num r' <- (evalM e r);
                            return( Num (l' - r') )
                        }
evalM e (And l r) = do    {
                            Boolean l' <- (evalM e l);
                            Boolean r' <- (evalM e r);
                            return( Boolean (l' && r') )
                        }
evalM e (Leq l r) = do    {
                            Num l' <- (evalM e l);
                            Num r' <- (evalM e r);
                            return( Boolean (l' <= r') )
                        }
evalM e (IsZero x) = do   {
                            Num v <- (evalM e x);
                            return( Boolean (v == 0) )
                        }
evalM e (If c t f) = do   {
                            Boolean v <- (evalM e c);
                            if (v==True) then (evalM e t) else (evalM e f)
                        }
evalM e (Bind i v b) = do {
                          v' <- (evalM e v) ;
                          evalM ((i,v'):e) b
                        }
evalM e (Id i) = lookup i e

testBBAE :: BBAE -> Bool
testBBAE expr = (evalM [] expr == evalS expr)

typeofM :: Cont -> BBAE -> (Maybe TBBAE)
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

typeofM c (And l r) = do    {
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


evalT :: BBAE -> (Maybe BBAE)
evalT bbae = let env = [] in
              do  {
                    typeofM env bbae;
                    evalM env bbae
                  }


parseBBAE = parseString expr

solveS = evalS . parseBBAE

solveMEnv a = evalM a . parseBBAE
solveM = evalM [] . parseBBAE

testMS = testBBAE . parseBBAE

solveTypeofM = typeofM [] . parseBBAE

solveEvalT = evalT . parseBBAE

main = do
  putStrLn $ show $ solveEvalT "bind x = 0 in true && isZero x"
