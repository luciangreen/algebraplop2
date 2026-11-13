-- | Positional formulas with exact rational arithmetic.
--
-- A position is a vector of integer indices (one index for a sequence,
-- several for a table).  Candidate formulas are fitted exactly (Gaussian
-- elimination over the rationals), must reproduce held-out samples they were
-- not fitted on, and are ranked by a description-length penalty, so the
-- result is deterministic: one answer.
module AlgebraPLOp2.Algebra
  ( Sample
  , Formula(..)
  , Found(..)
  , discover
  , evalF
  , fitsAll
  , penalty
  , formulaTerm
  , formulaFromTerm
  , exprTerm
  , showFormula
  , solveLinear
  , inversePositions
  ) where

import Data.List (sortOn, foldl')
import Data.Ratio
import Detlog2.Pretty (showTermQ)
import Detlog2.Term

type Sample = ([Integer], Integer)    -- position, value

data Formula
  = Poly [([Int], Rational)]          -- ^ sum of coefficient * product of index^exponent
  | Geo Rational Integer Rational     -- ^ a * b^i + c (one index)
  | Periodic Int [Formula]            -- ^ formula (i mod p): applied to i
  deriving (Eq, Show)

data Found = Found
  { fFormula :: Formula
  , fFitted :: Int                    -- ^ samples used to fit
  , fHeldOut :: Int                   -- ^ samples it reproduces without being fitted on them
  , fPenalty :: Integer
  } deriving (Show)

evalF :: Formula -> [Integer] -> Rational
evalF f pos = case f of
  Poly terms -> sum [ c * fromIntegral (product (zipWith (^) pos es)) | (es, c) <- terms ]
  Geo a b c -> case pos of
    [i] | i >= 0 -> a * fromIntegral (b ^ i) + c
        | otherwise -> a / fromIntegral (b ^ negate i) + c
    _ -> 0
  Periodic p fs -> case pos of
    [i] -> evalF (fs !! fromIntegral (i `mod` fromIntegral p)) pos
    _ -> 0

fitsAll :: Formula -> [Sample] -> Bool
fitsAll f = all (\(pos, v) -> evalF f pos == fromIntegral v)

-- | Description length: structure plus the size of every coefficient.
penalty :: Formula -> Integer
penalty f = case f of
  Poly terms -> 2 * fromIntegral (length [ () | (_, c) <- terms, c /= 0 ])
                + sum [ fromIntegral (sum es) | (es, c) <- terms, c /= 0 ]
                + sum [ size c | (_, c) <- terms, c /= 0 ]
  Geo a b c -> 3 + size a + size (fromIntegral b) + size c
  Periodic p fs -> 4 * fromIntegral p + sum (map penalty fs)
  where
    size r = bits (numerator r) + bits (denominator r) - 1
    bits n = fromIntegral (length (takeWhile (> 0) (iterate (`div` 2) (abs n)))) + 1

-- | Exact solution of A x = b over the rationals, if the system is
-- consistent and has a unique solution.
solveLinear :: [[Rational]] -> [Rational] -> Maybe [Rational]
solveLinear rows rhs = go 0 (zipWith (\r v -> r ++ [v]) rows rhs)
  where
    n = case rows of
      (r : _) -> length r
      [] -> 0
    go col m
      | col == n = if all (\r -> all (== 0) (take n r) <= (last r == 0)) m
                     then Just [ last (m !! i) | i <- [0 .. n - 1] ] else Nothing
      | otherwise = case [ i | (i, r) <- zip [0 ..] m, i >= col, r !! col /= 0 ] of
          [] -> Nothing
          (p : _) ->
            let swapped = swap col p m
                pr = swapped !! col
                pv = pr !! col
                prow = map (/ pv) pr
                elim i r | i == col = prow
                         | otherwise = let f = r !! col in zipWith (\a b -> a - f * b) r prow
            in go (col + 1) (zipWith elim [0 ..] swapped)
    swap i j xs | i == j = xs
                | otherwise = [ pick k x | (k, x) <- zip [0 ..] xs ]
      where pick k x | k == i = xs !! j
                     | k == j = xs !! i
                     | otherwise = x

-- | Monomials over m indices, in order of total degree up to d.
monomials :: Int -> Int -> [[Int]]
monomials m d = sortOn (\e -> (sum e, reverse e)) [ e | e <- vectors m, sum e <= d ]
  where
    vectors 0 = [[]]
    vectors k = [ x : r | x <- [0 .. d], r <- vectors (k - 1) ]

-- | Fit a polynomial with the given monomials on the first samples (as many
-- as monomials, linearly independent), then require the others to match.
fitPoly :: [[Int]] -> [Sample] -> Maybe Found
fitPoly basis samples = do
  let k = length basis
      row (pos, _) = [ fromIntegral (product (zipWith (^) pos es)) | es <- basis ]
      chosen = chooseIndependent k samples
  fitted <- chosen
  coeffs <- solveLinear (map row fitted) [ fromIntegral v | (_, v) <- fitted ]
  let f = Poly (filter ((/= 0) . snd) (zip basis coeffs))
      heldOut = length samples - k
  if heldOut >= 1 && fitsAll f samples then Just (Found f k heldOut (penalty f)) else Nothing
  where
    -- the first k samples whose rows are independent
    chooseIndependent k ss = go' [] ss
      where
        rowOf (pos, _) = [ fromIntegral (product (zipWith (^) pos es)) :: Rational | es <- basis ]
        go' acc _ | length acc == k = Just (reverse acc)
        go' _ [] = Nothing
        go' acc (s : rest)
          | independent (map rowOf (reverse (s : acc))) = go' (s : acc) rest
          | otherwise = go' acc rest
        independent rs = rank rs == length rs
    rank rs = length (filter (any (/= 0)) (echelon rs))
    echelon [] = []
    echelon rs = case [ r | r <- rs, not (null r), head r /= 0 ] of
      [] -> echelon [ tail r | r <- rs, not (null r), not (null (tail r)) ]
      (p : _) ->
        let others = [ zipWith (\a b -> a - (head r / head p) * b) (tail r) (tail p)
                     | r <- rs, r /= p ]
        in p : echelon (filter (not . null) others)

-- | a * b^i + c from consecutive single-index samples.
fitGeo :: [Sample] -> Maybe Found
fitGeo samples = case samples of
  (([i0], x0) : ([i1], x1) : ([i2], x2) : _ : _)
    | i1 == i0 + 1 && i2 == i1 + 1 && x1 /= x0 ->
        let d1 = fromIntegral (x1 - x0) :: Rational
            d2 = fromIntegral (x2 - x1)
            br = d2 / d1
        in if denominator br == 1 && numerator br `notElem` [0, 1]
             then let b = numerator br
                      a = d1 / (fromIntegral b ^^ i0 * fromIntegral (b - 1))
                      c = fromIntegral x0 - a * fromIntegral b ^^ i0
                      f = Geo a b c
                  in if fitsAll f samples then Just (Found f 3 (length samples - 3) (penalty f)) else Nothing
             else Nothing
  _ -> Nothing

-- | Different affine formulas for i mod 2 = 0 and 1 (each with held-out samples).
fitPeriodic :: [Sample] -> Maybe Found
fitPeriodic samples = do
  let byClass r = [ s | s@([i], _) <- samples, i `mod` 2 == r ]
  fs <- mapM (\r -> best [ fitPoly (monomials 1 d) (byClass r) | d <- [0, 1] ]) [0, 1]
  let f = Periodic 2 (map fFormula fs)
  if fitsAll f samples
    then Just (Found f (sum (map fFitted fs)) (sum (map fHeldOut fs)) (penalty f))
    else Nothing
  where best xs = case [ x | Just x <- xs ] of
          [] -> Nothing
          ys -> Just (head (sortOn fPenalty ys))

-- | The best formula for the samples, or Nothing (no_formula).
discover :: [Sample] -> Maybe Found
discover samples
  | null samples = Nothing
  | otherwise =
      let m = length (fst (head samples))
          maxDeg = if m == 1 then 4 else 2
          polys = [ fitPoly (monomials m d) samples | d <- [0 .. maxDeg] ]
          others = if m == 1 then [fitGeo sorted, fitPeriodic sorted] else []
          sorted = sortOn fst samples
          cands = [ f | Just f <- polys ++ others ]
      in case sortOn (\f -> (fPenalty f, fFitted f)) cands of
           (f : _) -> Just f
           [] -> Nothing

-- | Positions i (single index, i >= lo) where the formula takes value v,
-- searched up to a bound.
inversePositions :: Formula -> Integer -> Integer -> Integer -> [Integer]
inversePositions f lo hi v = [ i | i <- [lo .. hi], evalF f [i] == fromIntegral v ]

-- ---------------------------------------------------------------------------
-- Terms

ratT :: Rational -> Term
ratT r = Comp "/" [Int (numerator r), Int (denominator r)]

formulaTerm :: Formula -> Term
formulaTerm f = case f of
  Poly terms -> Comp "poly" [mkList [ Comp "m" [mkList (map (Int . fromIntegral) es) (Atom "[]"), ratT c] | (es, c) <- terms ] (Atom "[]")]
  Geo a b c -> Comp "geo" [ratT a, Int b, ratT c]
  Periodic p fs -> Comp "periodic" [Int (fromIntegral p), mkList (map formulaTerm fs) (Atom "[]")]

formulaFromTerm :: Term -> Maybe Formula
formulaFromTerm t = case t of
  Comp "poly" [l] -> Poly <$> (listT l >>= mapM mono)
  Comp "geo" [a, Int b, c] -> Geo <$> rat a <*> pure b <*> rat c
  Comp "periodic" [Int p, l] -> Periodic (fromIntegral p) <$> (listT l >>= mapM formulaFromTerm)
  _ -> Nothing
  where
    mono (Comp "m" [es, c]) = (,) <$> (listT es >>= mapM int) <*> rat c
    mono _ = Nothing
    int (Int i) = Just (fromIntegral i)
    int _ = Nothing
    rat (Comp "/" [Int n, Int d]) | d /= 0 = Just (n % d)
    rat _ = Nothing
    listT (Atom "[]") = Just []
    listT (Comp "." [h, r]) = (h :) <$> listT r
    listT _ = Nothing

-- | An integer arithmetic expression for is/2 over index variables.  The
-- formula is integer-valued where it is used (it reproduces integer
-- values), so the division by the common denominator is exact.
exprTerm :: Formula -> [Term] -> Term
exprTerm f vars = case f of
  Poly terms ->
    let d = foldl' lcm 1 [ denominator c | (_, c) <- terms ]
        num = sumT [ timesT (Int (numerator (c * fromIntegral d))) (monoT es) | (es, c) <- terms ]
    in if d == 1 then num else Comp "//" [num, Int d]
  Geo a b c ->
    let d = foldl' lcm 1 [denominator a, denominator c]
        i = head vars
        pw = Comp "^" [Int b, i]
        num = sumT [timesT (Int (numerator (a * fromIntegral d))) pw, Int (numerator (c * fromIntegral d))]
    in if d == 1 then num else Comp "//" [num, Int d]
  Periodic p fs ->
    -- (i mod p =:= r) selects the formula; written as a sum of selected terms
    let i = head vars
        sel r = Comp "-" [Int 1, Comp "min" [Int 1, Comp "abs" [Comp "-" [Comp "mod" [i, Int (fromIntegral p)], Int r]]]]
    in sumT [ timesT (sel r) (exprTerm g vars) | (r, g) <- zip [0 ..] fs ]
  where
    monoT es = case concat [ replicate e v | (v, e) <- zip vars es ] of
      [] -> Int 1
      xs -> foldl1 (\a b -> Comp "*" [a, b]) xs
    timesT (Int 1) x = x
    timesT c (Int 1) = c
    timesT c x = Comp "*" [c, x]
    sumT [] = Int 0
    sumT xs = foldl1 (\a b -> Comp "+" [a, b]) xs

-- | A readable formula over index names i, j, k, ...
showFormula :: Formula -> String
showFormula f = showTermQ (exprTerm f [ Atom [c] | c <- "ijklmn" ])
