-- | algebraplop2 command line.
module Main (main) where

import Control.Exception (IOException, try)
import Control.Monad (forM_, unless)
import Data.Char (isDigit, isSpace)
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map.Strict as M
import Data.Ratio
import System.Environment (getArgs, lookupEnv)
import System.Exit
import System.IO
import System.Process (readProcessWithExitCode)

import AlgebraPLOp2.Algebra
import AlgebraPLOp2.Program
import AlgebraPLOp2.Proof
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Term

usage :: String
usage = unlines
  [ "algebraplop2 - positional formulas, inverses and splice-index loops, with proofs"
  , ""
  , "  algebraplop2 samples SAMPLES [--mnns DIR]"
  , "        SAMPLES: values at positions 0, 1, ... (\"2,4,8,16\") or position-value"
  , "        pairs (\"[0,0]-1 [0,1]-2 [1,0]-3 ...\"); prints the formula or no_formula"
  , "  algebraplop2 program FILE NAME/2 [--domain LO..HI] [--mnns DIR] [-o OUT]"
  , "        the formula of NAME(Position, Value): proved by induction when NAME is a"
  , "        first-order recurrence, else verified on LO..HI; writes NAME__formula,"
  , "        NAME__inverse (affine formulas), NAME__loop for findall/between loops,"
  , "        and r_spec facts"
  , "  algebraplop2 proof-check FILE OUT OUT.proof"
  , ""
  , "Every output is proof-gated: it is written only if AlgebraPLOp2.Proof accepts its proof."
  ]

data Flags = Flags { fDomain :: Maybe (Integer, Integer), fMnns :: Maybe FilePath, fOut :: Maybe FilePath, fPos :: [String] }

parseFlags :: [String] -> Either String Flags
parseFlags = go (Flags Nothing Nothing Nothing [])
  where
    go f [] = Right f { fPos = reverse (fPos f) }
    go f ("--domain" : d : r) = case break (== '.') d of
      (lo, '.' : '.' : hi) -> go f { fDomain = Just (read lo, read hi) } r
      _ -> Left "--domain expects LO..HI"
    go f ("--mnns" : d : r) = go f { fMnns = Just d } r
    go f ("-o" : o : r) = go f { fOut = Just o } r
    go _ (x : _) | "--" `isPrefixOf` x = Left ("unknown option " ++ x)
    go f (x : r) = go f { fPos = x : fPos f } r

die' :: String -> IO a
die' m = hPutStrLn stderr ("algebraplop2: " ++ m) >> exitWith (ExitFailure 1)

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  case args of
    [] -> putStr usage
    ("help" : _) -> putStr usage
    (cmd : rest) -> either die' (dispatch cmd) (parseFlags rest)

dispatch :: String -> Flags -> IO ()
dispatch cmd fl = case (cmd, fPos fl) of
  ("samples", ws@(_ : _)) -> do
    samples <- either die' return (parseSamples (unwords ws))
    case discover samples of
      Nothing -> do
        putStrLn "no_formula"
        mnnsLine fl samples
      Just found -> do
        let f = fFormula found
            step = Comp "fit" [samplesT samples, formulaTerm f]
        _ <- either (\e -> die' ("proof rejected: " ++ e)) return (checkAlgebraProof emptyProgram [step] emptyProgram)
        putStrLn ("formula: " ++ showFormula f)
        putStrLn ("term: " ++ showTermQ (formulaTerm f))
        putStrLn ("verified_on: " ++ show (length samples) ++ " samples (" ++ show (fHeldOut found)
                  ++ " held out), description length " ++ show (fPenalty found))
        mnnsLine fl samples
        putStrLn "proof accepted: fit"
  ("program", [file, keyS]) -> programCmd fl file keyS
  ("proof-check", [file, out, proofFile]) -> do
    src <- loadProgram file
    prog <- loadProgram out
    steps <- readFile proofFile >>= either (\e -> die' (proofFile ++ ": " ++ e)) return . readProof
    either (\e -> die' ("proof rejected: " ++ e)) (mapM_ putStrLn) (checkAlgebraProof src steps prog)
  _ -> die' ("bad arguments\n" ++ usage)

loadProgram :: FilePath -> IO Program
loadProgram path = readFile path >>= either (\e -> die' (path ++ ": " ++ e)) return . parseProgram

samplesT :: [Sample] -> Term
samplesT ss = mkList [ Comp "s" [mkList (map Int pos) (Atom "[]"), Int v] | (pos, v) <- ss ] (Atom "[]")

-- | "2,4,8,16" or "[0,0]-1 [0,1]-2".
parseSamples :: String -> Either String [Sample]
parseSamples s
  | '-' `elem` dropNeg s && '[' `elem` s = mapM pair (words s)
  | otherwise = Right (zip [ [i] | i <- [0 ..] ] (map read (splitOn ',' (filter (not . isSpace) s))))
  where
    dropNeg = filter (/= ' ')
    pair w = case break (== ']') w of
      ('[' : pos, ']' : '-' : v) | all (\c -> isDigit c || c == '-') v ->
        Right (map read (splitOn ',' pos), read v)
      _ -> Left ("bad sample " ++ w)
    splitOn c xs = case break (== c) xs of
      (a, _ : rest) -> a : splitOn c rest
      (a, []) -> [a]

-- | mnns AlgebraPLOp's answer on the same values, for comparison.
mnnsLine :: Flags -> [Sample] -> IO ()
mnnsLine fl samples = do
  dir <- maybe (lookupEnv "MNNS_DIR") (return . Just) (fMnns fl)
  case dir of
    Nothing -> return ()
    Just d | all (\(pos, _) -> length pos == 1) samples -> do
      let goal = "use_module('" ++ d ++ "/prolog/algebraplop/algebraplop'), mnn_algebraplop:infer_sequence_formula(["
                 ++ intercalate "," (map (show . snd) samples) ++ "], F), writeq(F), nl"
      r <- try (readProcessWithExitCode "swipl" ["-q", "-g", goal, "-t", "halt"] "") :: IO (Either IOException (ExitCode, String, String))
      case r of
        Right (ExitSuccess, out, _) -> putStrLn ("mnns AlgebraPLOp: " ++ takeWhile (/= '\n') out)
        _ -> putStrLn "mnns AlgebraPLOp: not available"
    Just _ -> putStrLn "mnns AlgebraPLOp: single-index samples only"

programCmd :: Flags -> FilePath -> String -> IO ()
programCmd fl file keyS = do
  src <- loadProgram file
  key@(p, n) <- case break (== '/') keyS of
    (f, '/' : a) -> return (f, read a)
    _ -> die' "expected NAME/2"
  unless (n == 2) $ die' "positions are read from a predicate NAME(Position, Value)"
  let rec' = extractRecurrence src key
      (lo, hi) = case (fDomain fl, rec') of
        (Just d, _) -> d
        (Nothing, Just r) -> (rBase r, rBase r + 12)
        (Nothing, Nothing) -> (0, 12)
  samples <- either die' return (samplePredicate src key lo hi)
  found <- maybe (putStrLn ("no_formula for " ++ keyS ++ " on " ++ show lo ++ ".." ++ show hi) >> exitWith (ExitFailure 1)) return (discover samples)
  let f = fFormula found
      provedByInduction = maybe False (`inductionHolds` f) rec'
      formulaC = if provedByInduction
                   then formulaClause p f (maybe lo rBase rec') Nothing
                   else formulaClause p f lo (Just hi)
      evidenceStep = if provedByInduction
        then Comp "induction" [keyT key, formulaTerm f, clauseT formulaC]
        else Comp "exhaustive" [keyT key, Int lo, Int hi, formulaTerm f, clauseT formulaC]
      evidence = if provedByInduction
        then Comp "proved" [Atom "induction"]
        else Comp "verified_on" [Comp ".." [Int lo, Int hi]]
      domainLo = if provedByInduction then maybe lo rBase rec' else lo
      domainHi = if provedByInduction then Nothing else Just hi
      affine = case f of
        Poly terms | all (\(es, c) -> length es == 1 && head es <= 1 && denominator c == 1) terms ->
          let coef e = sum [ numerator c | (es, c) <- terms, es == [e] ] in
          if coef 1 /= 0 then Just (coef 1, coef 0) else Nothing
        _ -> Nothing
      inverseC = fmap (\(a, b) -> inverseClause p a b domainLo domainHi) affine
      inverseStep = fmap (\c -> Comp "inverse" [keyT key, formulaTerm f, Int domainLo, maybe (Atom "inf") Int domainHi, clauseT c]) inverseC
      -- splice-index loops (only for a formula proved for every position)
      allSrc = concat [ cs | (_, cs) <- programClauses src ]
      loops = if not provedByInduction then [] else
        [ (i, c') | (i, c) <- zip [1 :: Integer ..] allSrc
                  , let c' = replaceLoopsIn p (maybe lo rBase rec') c
                  , clauseT c' /= clauseT c ]
      loopC = loopClause p
      loopSteps = [ Comp "loop" [keyT key, Int i, clauseT c', clauseT loopC] | (i, c') <- loops ]
      rspec = Comp "r_spec" [ keyT key, Comp "position" [Int 1], Comp "value" [Int 2]
                            , Comp "formula" [formulaTerm f], Comp "expression" [exprTerm f [Atom "i"]], evidence ]
      steps = [evidenceStep] ++ maybe [] (: []) inverseStep ++ loopSteps ++ [rspec]
      replaced = map fst loops
      outClauses = [ maybe c id (lookup i loops) | (i, c) <- zip [1 ..] allSrc ]
                   ++ [formulaC] ++ maybe [] (: []) inverseC ++ [ loopC | not (null loops) ]
                   ++ [Clause rspec (Atom "true") (maxVarId rspec + 1)]
      outProg = programFromClauses outClauses
      _ = replaced
  report <- either (\e -> die' ("proof rejected: " ++ e)) return (checkAlgebraProof src steps outProg)
  putStrLn ("formula: " ++ keyS ++ " at position i = " ++ showFormula f)
  putStrLn ("evidence: " ++ showTermQ evidence ++ (if provedByInduction then "" else " (no first-order recurrence proof)"))
  forM_ inverseC $ \_ -> putStrLn ("inverse: " ++ p ++ "__inverse(V, N)")
  unless (null loops) $ putStrLn ("splice-index loops: " ++ show (length loops) ++ " findall/between loop(s) replaced by " ++ p ++ "__loop/3")
  mnnsLine fl samples
  mapM_ putStrLn report
  let text = unlines
        [ "% algebraplop2: positional formula for " ++ keyS ++ ", from " ++ file
        , "% " ++ showTermQ evidence ++ "; the proof is in the .proof file."
        , "" ] ++ showProgram outProg
  case fOut fl of
    Nothing -> putStr text
    Just o -> do
      writeFile o text
      writeFile (o ++ ".proof") (proofText steps)
      hPutStrLn stderr ("wrote " ++ o ++ " and " ++ o ++ ".proof")

replaceLoopsIn :: String -> Integer -> Clause -> Clause
replaceLoopsIn p base (Clause h b nv) = Clause h (go b) nv
  where
    go t = case t of
      Comp "findall" [v, Comp "," [Comp "between" [l, hh, i], Comp q [i', v']], vs]
        | q == p && i == i' && v == v' && isVar i && isVar v -> loopGoal p base l hh vs t
      Comp op [x, y] | op `elem` [",", ";", "->"] -> Comp op [go x, go y]
      _ -> t

keyT :: PredKey -> Term
keyT (f, n) = Comp "/" [Atom f, Int (fromIntegral n)]

clauseT :: Clause -> Term
clauseT (Clause h b _) = Comp ":-" [h, b]

_unused :: M.Map Int Int
_unused = M.empty
