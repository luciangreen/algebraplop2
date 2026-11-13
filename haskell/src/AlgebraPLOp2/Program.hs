-- | Positions from programs: sampling a predicate p(I, V) and proving its
-- formula by induction when p is a first-order recurrence.
module AlgebraPLOp2.Program
  ( Recurrence(..)
  , extractRecurrence
  , inductionHolds
  , samplePredicate
  , PolyN
  , polyEval
  ) where

import qualified Data.Map.Strict as M
import Data.Ratio
import AlgebraPLOp2.Algebra
import Detlog2.Builtins (Ev(..))
import Detlog2.Interp
import Detlog2.Parser
import Detlog2.Prelude
import Detlog2.Term

-- | A polynomial in N: coefficients of N^0, N^1, ...
type PolyN = [Rational]

-- | p(B, VB).   p(N, V) :- N > B, N1 is N - 1, p(N1, V1), V is A * V1 + G(N).
data Recurrence = Recurrence
  { rBase :: Integer
  , rBaseValue :: Integer
  , rA :: Rational
  , rG :: PolyN
  } deriving (Eq, Show)

polyEval :: PolyN -> Rational -> Rational
polyEval cs x = foldr (\c acc -> c + x * acc) 0 cs

-- | Recognise a first-order recurrence in the source clauses of p/2 (in
-- either clause order; the goals of the recursive clause in this order).
extractRecurrence :: Program -> PredKey -> Maybe Recurrence
extractRecurrence prog key@(f, 2) = case M.findWithDefault [] key (progPreds prog) of
  [c1, c2] -> case (baseOf c1, stepOf c2) of
    (Just (b, vb), Just (b', a, g)) | b == b' -> Just (Recurrence b vb a g)
    _ -> case (baseOf c2, stepOf c1) of
      (Just (b, vb), Just (b', a, g)) | b == b' -> Just (Recurrence b vb a g)
      _ -> Nothing
  _ -> Nothing
  where
    baseOf (Clause (Comp _ [Int b, Int vb]) (Atom "true") _) = Just (b, vb)
    baseOf _ = Nothing
    stepOf (Clause (Comp _ [n@(Var _ _), v@(Var _ _)]) body _) = case conjList body of
      [Comp ">" [n', Int b], Comp "is" [n1@(Var _ _), Comp "-" [n'', Int 1]], Comp g [n1', v1@(Var _ _)], Comp "is" [v', e]]
        | n' == n && n'' == n && n1' == n1 && g == f && v' == v && v1 /= v && n1 /= n ->
            fmap (\(a, gp) -> (b, a, gp)) (linearIn v1 n n1 e)
      _ -> Nothing
    stepOf _ = Nothing
extractRecurrence _ _ = Nothing

-- | E as A * V1 + G(N), where N1 stands for N - 1.
linearIn :: Term -> Term -> Term -> Term -> Maybe (Rational, PolyN)
linearIn v1 n n1 e = do
  p <- poly e
  -- p maps the degree in V1 to a polynomial in N
  let deg0 = M.findWithDefault [] 0 p
      deg1 = M.findWithDefault [] 1 p
  if any (> 1) (M.keys (M.filter (any (/= 0)) p)) then Nothing else
    case trim deg1 of
      [] -> Just (0, trim deg0)
      [a] -> Just (a, trim deg0)
      _ -> Nothing
  where
    trim = reverse . dropWhile (== 0) . reverse
    -- polynomials in V1 (keys) with coefficients that are polynomials in N
    poly t = case t of
      Int i -> Just (M.singleton 0 [fromIntegral i])
      _ | t == v1 -> Just (M.singleton 1 [1])
        | t == n -> Just (M.singleton 0 [0, 1])
        | t == n1 -> Just (M.singleton 0 [-1, 1])
      Comp "+" [a, b] -> addP <$> poly a <*> poly b
      Comp "-" [a, b] -> addP <$> poly a <*> (negP <$> poly b)
      Comp "-" [a] -> negP <$> poly a
      Comp "*" [a, b] -> mulP <$> poly a <*> poly b
      Comp "^" [a, Int k] | k >= 0 && k <= 6 -> poly a >>= \pa -> Just (foldr (\_ acc -> mulP pa acc) (M.singleton 0 [1]) [1 .. k])
      Comp "**" [a, Int k] | k >= 0 && k <= 6 -> poly (Comp "^" [a, Int k])
      _ -> Nothing
    addP = M.unionWith addN
    negP = M.map (map negate)
    mulP p q = M.fromListWith addN [ (i + j, mulN a b) | (i, a) <- M.toList p, (j, b) <- M.toList q ]
    addN a b = let l = max (length a) (length b)
               in zipWith (+) (a ++ replicate (l - length a) 0) (b ++ replicate (l - length b) 0)
    mulN a b = [ sum [ a !! i * b !! (k - i) | i <- [0 .. k], i < length a, k - i < length b ]
               | k <- [0 .. length a + length b - 2] ]

-- | f(B) = VB, and f(n) = A f(n-1) + G(n) for all n.  For a polynomial f
-- the difference is a polynomial of degree at most D, so it is zero when it
-- is zero at D + 1 points; for a f = a b^n + c it is checked symbolically.
inductionHolds :: Recurrence -> Formula -> Bool
inductionHolds (Recurrence b vb a g) f =
  evalF f [b] == fromIntegral vb && stepHolds
  where
    stepHolds = case f of
      Poly terms | all (\(es, _) -> length es == 1) terms ->
        let d = maximum (0 : length g : [ head es | (es, _) <- terms ]) + 1
            pts = [ fromIntegral b + 1 + fromIntegral k | k <- [0 .. d + 1] ] :: [Integer]
        in and [ evalF f [p] == a * evalF f [p - 1] + polyEval g (fromIntegral p) | p <- pts ]
      Geo aa bb c ->
        -- aa b^n + c = A (aa b^(n-1) + c) + G(n)  for all n
        (aa == 0 || fromIntegral bb == a) && all (== 0) (drop 1 g)
          && (if null g then 0 else head g) == c * (1 - a)
      _ -> False

-- | Values p(I, V) for I in lo..hi (first answer each), on the cutless
-- interpreter.
samplePredicate :: Program -> PredKey -> Integer -> Integer -> Either String [Sample]
samplePredicate prog (f, _) lo hi = mapM one [lo .. hi]
  where
    p = withPrelude prog
    one i = case firstAnswer (runGoal defaultOptions p (Comp f [Int i, Var 0 "V"]) 1) of
      Left e -> Left ("p(" ++ show i ++ ", V): " ++ e)
      Right (Just (Int v)) -> Right ([i], v)
      Right (Just t) -> Left ("p(" ++ show i ++ ", V) gave a non-integer " ++ show t)
      Right Nothing -> Left ("p(" ++ show i ++ ", V) failed")
    firstAnswer [] = Right Nothing
    firstAnswer (Out _ : r) = firstAnswer r
    firstAnswer (Err e : _) = Left e
    firstAnswer (Ans st : _) = Right (Just (resolve st (Var 0 "V")))

_unused :: Rational
_unused = 1 % 1
