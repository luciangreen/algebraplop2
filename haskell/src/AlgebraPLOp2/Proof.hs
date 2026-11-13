-- | Independent checker for algebraplop2 proofs.
--
-- Steps (Prolog terms, one per rewrite):
--
--   fit(Samples, Formula)                      verified_on: reproduces every sample,
--                                              with at least one held-out sample
--   induction(P/2, Formula, Clause)            proved: base case and step identity,
--                                              read off the source by evaluation
--   exhaustive(P/2, Lo, Hi, Formula, Clause)   verified_on(Lo..Hi): the source is
--                                              run on every position of the domain
--   inverse(P/2, Formula, Lo, Hi, Clause)      the inverse of an affine formula
--   loop(P/2, ClauseIndex, NewClause, LoopClause)
--                                              a splice-index loop replacing
--                                              findall/3 over between/3
--   r_spec(...)                                provenance facts
--
-- The checker does not use the discovery code: it evaluates the source's
-- own arithmetic (with detlog2's evaluator) to read the recurrence, and
-- runs the source to compare values.
module AlgebraPLOp2.Proof
  ( checkAlgebraProof
  , proofText
  , readProof
  , formulaClause
  , inverseClause
  , loopClause
  , loopGoal
  ) where

import Control.Monad (forM, forM_, unless)
import qualified Data.Map.Strict as M
import Data.Ratio
import qualified Data.IntMap.Strict as IM
import AlgebraPLOp2.Algebra
import Detlog2.Builtins (Ev(..), NumV(..), evalArith)
import Detlog2.Interp
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Prelude
import Detlog2.Reference (refRun)
import Detlog2.Term

type Check a = Either String a

ensure :: Bool -> String -> Check ()
ensure b m = unless b (Left m)

proofText :: [Term] -> String
proofText steps = unlines ("% algebraplop2 proof: one step per rewrite (see docs/proof_rules.md)."
                           : [ showTermQ s ++ "." | s <- steps ])

readProof :: String -> Either String [Term]
readProof src = do
  p <- parseProgram src
  return [ if clBody c == Atom "true" then clHead c else Comp ":-" [clHead c, clBody c]
         | (_, cs) <- programClauses p, c <- cs ]

-- ---------------------------------------------------------------------------
-- Templates (shared with the generator; they are checked against the
-- source by evaluation below)

-- | P__formula(N, V) :- integer(N), N >= Lo [, N =< Hi], V is Expr.
formulaClause :: String -> Formula -> Integer -> Maybe Integer -> Clause
formulaClause p f lo mhi =
  let n = Var 0 "N"
      v = Var 1 "V"
      guards = [Comp "integer" [n], Comp ">=" [n, Int lo]] ++ maybe [] (\hi -> [Comp "=<" [n, Int hi]]) mhi
  in Clause (Comp (p ++ "__formula") [n, v]) (mkConj (guards ++ [Comp "is" [v, exprTerm f [n]]])) 2

-- | P__inverse(V, N) for an affine formula a*N + b with integer a /= 0.
inverseClause :: String -> Integer -> Integer -> Integer -> Maybe Integer -> Clause
inverseClause p a b lo mhi =
  let v = Var 0 "V"
      n = Var 1 "N"
      d = Var 2 "D"
      goals = [ Comp "integer" [v], Comp "is" [d, Comp "-" [v, Int b]]
              , Comp "=:=" [Comp "mod" [d, Int a], Int 0], Comp "is" [n, Comp "//" [d, Int a]]
              , Comp ">=" [n, Int lo] ] ++ maybe [] (\hi -> [Comp "=<" [n, Int hi]]) mhi
  in Clause (Comp (p ++ "__inverse") [v, n]) (mkConj goals) 3

-- | P__loop(I, H, Vs): the values at positions I..H, by the formula.
loopClause :: String -> Clause
loopClause p =
  let i = Var 0 "I"
      h = Var 1 "H"
      vs = Var 2 "Vs"
      v = Var 3 "V"
      i1 = Var 4 "I1"
      vs1 = Var 5 "Vs1"
      body = Comp ";" [ Comp "->" [Comp ">" [i, h], Comp "=" [vs, Atom "[]"]]
                      , mkConj [ Comp (p ++ "__formula") [i, v], Comp "is" [i1, Comp "+" [i, Int 1]]
                               , Comp "=" [vs, Comp "." [v, vs1]], Comp (p ++ "__loop") [i1, h, vs1] ] ]
  in Clause (Comp (p ++ "__loop") [i, h, vs]) body 6

-- | The goal replacing findall(V, (between(L, H, I), p(I, V)), Vs).
loopGoal :: String -> Integer -> Term -> Term -> Term -> Term -> Term
loopGoal p base l h vs original =
  Comp ";" [ Comp "->" [ mkConj [Comp "integer" [l], Comp "integer" [h], Comp ">=" [l, Int base]]
                       , Comp (p ++ "__loop") [l, h, vs] ]
           , original ]

-- ---------------------------------------------------------------------------
-- Checking

-- | Check every step against the source program, and that the output
-- program is the source with exactly the justified changes.
checkAlgebraProof :: Program -> [Term] -> Program -> Check [String]
checkAlgebraProof src steps out = do
  proved <- fmap concat $ forM steps $ \s -> case s of
    Comp "induction" [kt, ft, clT] -> do
      key <- keyOf kt
      f <- formulaOf ft
      cl <- asClause clT
      base <- checkInduction src key f
      ensure (variant0 (clauseTerm cl) (clauseTerm (formulaClause (fst key) f base Nothing)))
             (showKey key ++ ": the formula clause is not the template")
      sampleAgree key cl [base .. base + 12]
      return [(key, base)]
    _ -> return []
  let provedMap = M.fromList proved
  justified <- fmap concat $ forM steps $ \s -> case s of
    Comp "fit" [samplesT, ft] -> do
      f <- formulaOf ft
      samples <- samplesOf samplesT
      ensure (fitsAll f samples) "fit: the formula does not reproduce every sample"
      ensure (length samples > params f) "fit: no held-out sample (more parameters than samples allow)"
      return []
    Comp "induction" [_, _, clT] -> (: []) <$> asClause clT
    Comp "exhaustive" [kt, Int lo, Int hi, ft, clT] -> do
      key <- keyOf kt
      f <- formulaOf ft
      cl <- asClause clT
      ensure (variant0 (clauseTerm cl) (clauseTerm (formulaClause (fst key) f lo (Just hi))))
             (showKey key ++ ": the formula clause is not the template")
      forM_ [lo .. hi] $ \i -> do
        v <- runSource src key i
        ensure (v == Just (evalF f [i])) (showKey key ++ ": the formula differs from the program at " ++ show i)
      sampleAgree key cl [lo .. hi]
      return [cl]
    Comp "inverse" [kt, ft, Int lo, hiT, clT] -> do
      key <- keyOf kt
      f <- formulaOf ft
      cl <- asClause clT
      let mhi = case hiT of
            Int hi -> Just hi
            _ -> Nothing
      (a, b) <- case f of
        Poly terms | all (\(es, c) -> length es == 1 && head es <= 1 && denominator c == 1) terms ->
          let coef e = sum [ numerator c | (es, c) <- terms, es == [e] ] in return (coef 1, coef 0)
        _ -> Left "inverse: only integer affine formulas are inverted"
      ensure (a /= 0) "inverse: constant formula"
      ensure (variant0 (clauseTerm cl) (clauseTerm (inverseClause (fst key) a b lo mhi))) "inverse: template"
      -- the formula's own step (induction or exhaustive) must cover the range
      ensure (M.member key provedMap || any (coversRange key lo mhi) steps) "inverse: the formula is not proved on this range"
      -- N |-> a N + b is injective, and a ((V - b) / a) + b = V when a divides V - b
      let hi = maybe (lo + 20) id mhi
          prog = withPrelude out
      forM_ [lo .. hi] $ \nI -> do
        let val = a * nI + b
        r <- firstOf prog (Comp (fst key ++ "__inverse") [Int val, Var 0 "N"]) (Var 0 "N")
        ensure (r == Just (Int nI)) ("inverse: " ++ show val ++ " does not give " ++ show nI)
      return [cl]
    Comp "loop" [kt, Int ci, newT, loopT] -> do
      key@(p, _) <- keyOf kt
      base <- maybe (Left ("loop: " ++ showKey key ++ " has no induction proof")) return (M.lookup key provedMap)
      newC <- asClause newT
      loopC <- asClause loopT
      ensure (variant0 (clauseTerm loopC) (clauseTerm (loopClause p))) "loop: loop template"
      -- the new clause is a source clause with each findall over between and p replaced
      let allSrc = concat [ cs | (_, cs) <- programClauses src ]
      ensure (ci >= 1 && fromIntegral ci <= length allSrc) "loop: no such clause"
      let old = allSrc !! (fromIntegral ci - 1)
      ensure (variant0 (clauseTerm newC) (clauseTerm (replaceLoops p base old)))
             "loop: the new clause is not the source clause with its loops replaced"
      return [newC, loopC]
    Comp "r_spec" _ -> return []
    _ -> Left ("unknown step " ++ take 80 (showTermQ s))
  -- the output is the source (with replaced clauses), plus justified clauses and r_spec facts
  let replacedIdx = [ fromIntegral ci | Comp "loop" [_, Int ci, _, _] <- steps ] :: [Int]
      srcClauses = [ c | (i, c) <- zip [1 ..] (concat [ cs | (_, cs) <- programClauses src ]), i `notElem` replacedIdx ]
      rspecs = [ Clause s (Atom "true") (maxVarId s + 1) | s@(Comp "r_spec" _) <- steps ]
      expected = srcClauses ++ uniq justified ++ rspecs
      outCls = concat [ cs | (_, cs) <- programClauses out ]
  ensure (length outCls == length expected) ("the output has " ++ show (length outCls) ++ " clauses, the proof justifies " ++ show (length expected))
  forM_ outCls $ \c -> ensure (any (\e -> variant0 (clauseTerm c) (clauseTerm e)) expected)
                              ("unjustified clause: " ++ showTermQ (clauseTerm c))
  return ["proof accepted: " ++ show (length steps) ++ " steps"]
  where
    variant0 = variant (emptyState 0)
    uniq [] = []
    uniq (c : cs) = c : uniq (filter (not . variant0 (clauseTerm c) . clauseTerm) cs)
    coversRange key lo mhi s = case s of
      Comp "exhaustive" [kt, Int l, Int h, _, _] -> keyOf kt == Right key && l <= lo && maybe False (<= h) mhi
      _ -> False
    sampleAgree key cl is = do
      let prog = withPrelude (programFromClauses (cl : concat [ cs | (_, cs) <- programClauses src ]))
      forM_ is $ \i -> do
        v <- runSource src key i
        r <- firstOf prog (Comp (fst key ++ "__formula") [Int i, Var 0 "V"]) (Var 0 "V")
        ensure (fmap Int (v >>= asInt) == r) (showKey key ++ ": the emitted clause differs from the program at " ++ show i)
    asInt r = if denominator r == 1 then Just (numerator r) else Nothing

-- | Replace findall(V, (between(L, H, I), p(I, V)), Vs) goals in a clause.
replaceLoops :: String -> Integer -> Clause -> Clause
replaceLoops p base (Clause h b nv) = Clause h (go b) nv
  where
    go t = case t of
      Comp "findall" [v, Comp "," [Comp "between" [l, hh, i], Comp q [i', v']], vs]
        | q == p && i == i' && v == v' && isVar i && isVar v -> loopGoal p base l hh vs t
      Comp op [x, y] | op `elem` [",", ";", "->"] -> Comp op [go x, go y]
      _ -> t

params :: Formula -> Int
params f = case f of
  Poly terms ->
    let m = case terms of
          ((es, _) : _) -> length es
          [] -> 1
        d = maximum (0 : [ sum es | (es, _) <- terms ])
    in length [ () | e <- vectors m d, sum e <= d ]
  Geo _ _ _ -> 3
  Periodic _ fs -> sum (map params fs)
  where
    vectors 0 _ = [[]]
    vectors k d = [ x : r | x <- [0 .. d], r <- vectors (k - 1) d ]

-- | Base case and step identity, read from the source by evaluating its
-- own arithmetic.  Returns the base position.
checkInduction :: Program -> PredKey -> Formula -> Check Integer
checkInduction src key@(p, _) f = do
  let cls = M.findWithDefault [] key (progPreds src)
      here = "induction for " ++ showKey key ++ ": "
  (base, vb, step) <- case cls of
    [c1, c2] | Just (b, vb) <- baseOf c1 -> return (b, vb, c2)
             | Just (b, vb) <- baseOf c2 -> return (b, vb, c1)
    _ -> Left (here ++ "expected a base clause p(B, V) and one recursive clause")
  (nT, vT, n1T, v1T, e) <- case step of
    Clause (Comp _ [n@(Var _ _), v@(Var _ _)]) body _ -> case conjList body of
      [Comp ">" [n', Int b], Comp "is" [n1@(Var _ _), Comp "-" [n'', Int 1]], Comp q [n1', v1@(Var _ _)], Comp "is" [v', ex]]
        | n' == n && n'' == n && n1' == n1 && q == p && v' == v && b == base && v1 /= v && n1 /= n && v1 /= n ->
            return (n, v, n1, v1, ex)
      _ -> Left (here ++ "the recursive clause is not N > B, N1 is N - 1, p(N1, V1), V is E")
    _ -> Left (here ++ "the recursive clause head")
  ensure (evalF f [base] == fromIntegral vb) (here ++ "base case")
  ensure (onlyVars [nT, n1T, v1T] e) (here ++ "E uses other variables")
  -- E evaluated at V1 = x and N = n
  let evalE x n = case evalArith (bindAll [(nT, Int n), (n1T, Int (n - 1)), (v1T, x)]) e of
        Right (NI i) -> Right (fromIntegral i :: Rational)
        Right (NF d) -> Right (toRational d)
        Left err -> Left err
      ratT r = Comp "/" [Int (numerator r), Int (denominator r)]
      _ = vT
      deg = degree e (case f of
                        Poly terms -> maximum (0 : [ sum es | (es, _) <- terms ])
                        _ -> 0)
      pts = [ base + 1 + k | k <- [0 .. fromIntegral deg + 2] ]
  -- linear in V1 with a constant coefficient: E(x) = A x + G(n)
  aVals <- forM pts $ \n -> do
    e0 <- either Left Right (evalE (Int 0) n)
    e1 <- either Left Right (evalE (Int 1) n)
    e2 <- either Left Right (evalE (Int 2) n)
    ensure (e2 - e0 == 2 * (e1 - e0)) (here ++ "E is not linear in V1")
    return (e1 - e0, e0)
  let a = fst (head aVals)
  ensure (all ((== a) . fst) aVals) (here ++ "the coefficient of V1 depends on N")
  case f of
    Poly _ -> forM_ pts $ \n -> do
      -- f(n) = E(f(n-1), n): a polynomial identity of degree <= deg, checked at deg+3 points
      let prev = evalF f [n - 1]
      en <- either Left Right (evalE (ratT prev) n)
      ensure (evalF f [n] == en) (here ++ "step identity fails at " ++ show n)
    Geo aa bb c -> do
      -- G(n) = c (1 - A) for all n, and aa = 0 or b = A: G has degree <= deg,
      -- so it is that constant when it is at deg+3 points
      forM_ aVals $ \(_, g) -> ensure (g == c * (1 - a)) (here ++ "G is not c (1 - A)")
      ensure (aa == 0 || fromIntegral bb == a) (here ++ "the base of the power is not A")
    _ -> Left (here ++ "only polynomial and a*b^n+c formulas are proved by induction")
  return base
  where
    baseOf (Clause (Comp _ [Int b, Int vb]) (Atom "true") _) = Just (b, vb)
    baseOf _ = Nothing
    bindAll bs = foldl (\st (v, t) -> maybe st id (unify v t st)) (emptyState 100000) bs
    onlyVars vs t = all (`elem` [ i | Var i _ <- vs ]) [ i | Var i _ <- termVarsOrdered t ]
    -- a bound on the degree in N, with V1 of degree dv
    degree t dv = case t of
      Int _ -> 0 :: Int
      Var _ _ -> 1 `max` dv
      Comp op [x, y] | op `elem` ["+", "-"] -> max (degree x dv) (degree y dv)
      Comp "*" [x, y] -> degree x dv + degree y dv
      Comp "^" [x, Int k] -> fromIntegral k * degree x dv
      Comp "**" [x, Int k] -> fromIntegral k * degree x dv
      Comp "-" [x] -> degree x dv
      _ -> 100

runSource :: Program -> PredKey -> Integer -> Check (Maybe Rational)
runSource src (p, _) i = do
  r <- firstRef (withPrelude src) (Comp p [Int i, Var 0 "V"]) (Var 0 "V")
  return (case r of
            Just (Int v) -> Just (fromIntegral v)
            _ -> Nothing)

firstRef :: Program -> Term -> Term -> Check (Maybe Term)
firstRef prog g v = go (refRun defaultOptions prog g 10)
  where
    go [] = Right Nothing
    go (Out _ : r) = go r
    go (Err e : _) = Left e
    go (Ans st : _) = Right (Just (resolve st v))

firstOf :: Program -> Term -> Term -> Check (Maybe Term)
firstOf prog g v = go (runGoal defaultOptions prog g 10)
  where
    go [] = Right Nothing
    go (Out _ : r) = go r
    go (Err e : _) = Left e
    go (Ans st : _) = Right (Just (resolve st v))

keyOf :: Term -> Check PredKey
keyOf (Comp "/" [Atom f, Int n]) = return (f, fromIntegral n)
keyOf t = Left ("bad predicate indicator " ++ showTermQ t)

showKey :: PredKey -> String
showKey (f, n) = f ++ "/" ++ show n

formulaOf :: Term -> Check Formula
formulaOf t = maybe (Left ("bad formula " ++ showTermQ t)) return (formulaFromTerm t)

samplesOf :: Term -> Check [Sample]
samplesOf t = listOf t >>= mapM one
  where
    one (Comp "s" [pos, Int v]) = do
      ps <- listOf pos
      is <- mapM (\x -> case x of
                          Int i -> return i
                          _ -> Left "bad position") ps
      return (is, v)
    one x = Left ("bad sample " ++ showTermQ x)

listOf :: Term -> Check [Term]
listOf (Atom "[]") = return []
listOf (Comp "." [h, r]) = (h :) <$> listOf r
listOf t = Left ("not a list: " ++ showTermQ t)

asClause :: Term -> Check Clause
asClause t = case t of
  Comp ":-" [h, b] -> return (Clause h b (maxVarId t + 1))
  h | isCallable h -> return (Clause h (Atom "true") (maxVarId t + 1))
  _ -> Left ("not a clause: " ++ showTermQ t)
