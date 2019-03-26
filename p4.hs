{-# LANGUAGE GADTs #-}


-- NAME -- Lane Gramling
-- KUID -- 2766765
-- Comments:
--    Known issue:
--     It seems like my Fix function is growing infinitely in some cases. It's using
--     the Definition from my notes that we went over in class, which we later deemed
--     incorrect. For some reason I can't seem to find my notes from that next lecture
--     though, and I haven't quite been able to sniff out the correct definition so I
--     am just living with the blemish for now. '
--
-- Instructions for use:
--    1) Load in p4.hs
--    2) Evaluate an FBAE using interp <FBAE>. Can also directly use the evaluator
--       and typechecker using evalM <env> <FBAE> and typeofM <env> <FBAE>
--



-- import Control.Monad

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
  ClosureV :: String -> FBAE -> Env -> FBAEVal
  deriving (Show,Eq)

-- Enviornment for statically scoped eval

type Env = [(String,FBAEVal)]


-- Lift Functions

-- Lift an Int operator to BBAEs
liftNum :: (Int -> Int -> Int) -> FBAEVal -> FBAEVal -> FBAEVal
liftNum op (NumV l) (NumV r) = (NumV (op l r)) -- op identifies the operator

-- Lift an Int operator with Bool results to FBAEVals
liftNumToBool :: (Int -> Int -> Bool) -> FBAEVal -> FBAEVal -> FBAEVal
liftNumToBool op (NumV l) (NumV r) = (BooleanV (op l r)) -- op identifies the operator

-- Lift a BooleanV Operator with Bool results to FBAEVals
liftBool :: (Bool -> Bool -> Bool) -> FBAEVal -> FBAEVal -> FBAEVal
liftBool op (BooleanV l) (BooleanV r) = (BooleanV (op l r)) -- op identifies the operator


-- Substitution function
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
subst i v (IsZero n) = (IsZero (subst i v n))
subst i v (If c t e) = (If (subst i v c) (subst i v t) (subst i v e))
subst i v (Id ii) = if i==ii then v else (Id ii)
subst i v (Lambda i' t b) = if i==i' then (Lambda i' t (subst i v b)) else (Lambda i' t b)
subst i v (Bind ii vv bb) = if i==ii
                            then (Bind ii (subst i v vv) bb)
                            else (Bind ii (subst i v vv) (subst i v bb))

-- Statically scoped eval

evalM :: Env -> FBAE -> (Maybe FBAEVal)
evalM env (Num x) = (Just (NumV x))
evalM env (Boolean b) = (Just (BooleanV b))
evalM env (Plus l r) = do a1 <- (evalM env l)
                          a2 <- (evalM env r)
                          return (liftNum (+) a1 a2)
evalM env (Minus l r) = do a1 <- (evalM env l)
                           a2 <- (evalM env r)
                           return (liftNum (-) a1 a2)
evalM env (Mult l r) = do a1 <- (evalM env l)
                          a2 <- (evalM env r)
                          return (liftNum (*) a1 a2)
evalM env (Div l r) = do a1 <- (evalM env l)
                         a2 <- (evalM env r)
                         return (liftNum (div) a1 a2)
evalM env (And l r) = do a1 <- (evalM env l)
                         a2 <- (evalM env r)
                         return (liftBool (&&) a1 a2)
evalM env (Or l r) = do a1 <- (evalM env l)
                        a2 <- (evalM env r)
                        return (liftBool (||) a1 a2)
evalM env (Leq l r) = do a1 <- (evalM env l)
                         a2 <- (evalM env r)
                         return (liftNumToBool (<=) a1 a2)
evalM env (IsZero n) = do nn <- (evalM env n)
                          return (liftNumToBool (==) nn (NumV 0))
evalM env (Bind i v b) = do vv <- (evalM env v)
                            evalM ((i,vv):env) b
evalM env (If c t e) = do (BooleanV vv) <- (evalM env c)
                          if (vv) then (evalM env t) else (evalM env e)
evalM env (App (Lambda i t b) v) = do { (ClosureV ii bb ee) <- (evalM env (Lambda i t b));
                                      vv <- (evalM env v);
                                      evalM ((ii,vv):ee) (bb)}
evalM env (Lambda i t b) = Just (ClosureV i b env)
evalM env (Fix f) = do (ClosureV i b e) <- (evalM env f)
                       evalM env (subst i (Fix (Lambda i (TNum) b)) b)
evalM env (Id id) = lookup id env
evalM _ _ = Nothing

-- Type inference function

type Cont = [(String,TFBAE)]

typeofM :: Cont -> FBAE -> (Maybe TFBAE)
typeofM cont (Num n) = Just TNum
typeofM cont (Boolean b) = Just TBool
typeofM cont (Plus l r) = do TNum <- (typeofM cont l)
                             TNum <- (typeofM cont r)
                             return TNum
typeofM cont (Minus l r) = do TNum <- (typeofM cont l)
                              TNum <- (typeofM cont r)
                              return TNum
typeofM cont (Mult l r) = do TNum <- (typeofM cont l)
                             TNum <- (typeofM cont r)
                             return TNum
typeofM cont (Div l r) = do TNum <- (typeofM cont l)
                            TNum <- (typeofM cont r)
                            return TNum
typeofM cont (And l r) = do TBool <- (typeofM cont l) -- Boolean Operands
                            TBool <- (typeofM cont r)
                            return TBool
typeofM cont (Or l r) = do TBool <- (typeofM cont l) -- Boolean Operands
                           TBool <- (typeofM cont r)
                           return TBool
typeofM cont (Leq l r) = do TNum <- (typeofM cont l) -- Numeric Operands
                            TNum <- (typeofM cont r)
                            return TBool
typeofM cont (IsZero n) = do TNum <- (typeofM cont n) -- Numeric Operand
                             return TBool
typeofM cont (Lambda i t b) = Just (t)
typeofM cont (App f v) = typeofM cont v
typeofM cont (Fix (Lambda i t b)) = Just (t)
typeofM cont (If c t e) = do c1 <- (typeofM cont c)
                             t1 <- (typeofM cont t)
                             e1 <- (typeofM cont e) -- Confirm then/else types match
                             if c1==TBool && t1==e1 then return t1 else Nothing
typeofM cont (Bind i v b) = do vv <- (typeofM cont v)
                               typeofM ((i,vv):cont) b
typeofM cont (Id id) = lookup id cont
-- typeofM _ _ = Nothing


-- Interpreter
-- Links together the typechecker with the evaluator, for robustness
interp :: FBAE -> (Maybe FBAEVal)
interp e = case (typeofM [] e) of
                Just _ -> (evalM [] e)
                Nothing -> Nothing

-- Factorial function for testing evalM and typeofM.  the type of test1 should
-- be TNum and the result of evaluating test1`should be (NumV 6).  Remember
-- that Just is used to return both the value and type.

test1 = (Bind "f" (Lambda "g" ((:->:) TNum TNum)
                    (Lambda "x" TNum (If (IsZero (Id "x")) (Num 1)
                                         (Mult (Id "x")
                                               (App (Id "g")
                                                    (Minus (Id "x")
                                                           (Num 1)))))))
         (App (Fix (Id "f")) (Num 3)))
