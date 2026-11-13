-- | End-to-end tests of the algebraplop2 command line.  Run by Build.hs.
module Main (main) where

import Data.IORef
import Data.List (isInfixOf)
import System.Directory (findExecutable)
import System.Environment (lookupEnv)
import System.Exit
import System.Process (readProcessWithExitCode)

main :: IO ()
main = do
  fails <- newIORef (0 :: Int)
  let report name ok detail = if ok
        then putStrLn ("PASS " ++ name)
        else do
          putStrLn ("FAIL " ++ name)
          putStrLn (unlines (map ("    " ++) (lines detail)))
          modifyIORef fails (+ 1)
      runP exe args = do
        (_, o, e) <- readProcessWithExitCode exe args ""
        return (o ++ e)
      expectWith exe name want args = do
        o <- runP exe args
        report name (want `isInfixOf` o) o
      expectNot name bad args = do
        o <- runP "./build/hs/algebraplop2" args
        report name (not (bad `isInfixOf` o)) o
      expect = expectWith "./build/hs/algebraplop2"
      expectD2 = expectWith "./build/hs/detlog2"

  -- discovery from samples ---------------------------------------------------------
  expect "samples: 2,4,8,16 is 2 * 2^i" "formula: 2 * 2 ^ i" ["samples", "2,4,8,16"]
  expectNot "samples: 2,4,8,16 is not piecewise" "periodic" ["samples", "2,4,8,16"]
  expect "samples: affine" "formula: 1 + 3 * i" ["samples", "1,4,7,10,13"]
  expect "samples: quadratic with a rational coefficient" "formula: (i + i * i) // 2" ["samples", "0,1,3,6,10,15"]
  expect "samples: primes have no formula" "no_formula" ["samples", "2,3,5,7,11"]
  expect "samples: too few samples for a held-out check" "no_formula" ["samples", "5,9"]
  expect "samples: two indices" "formula: 2 * i + j" ["samples", "[0,0]-0 [0,1]-1 [1,0]-2 [1,1]-3 [2,0]-4 [2,1]-5"]
  expect "samples: alternating" "periodic" ["samples", "0,10,2,20,4,30,6,40"]
  expect "samples: proof" "proof accepted: fit" ["samples", "1,4,7,10,13"]

  -- formulas of programs -------------------------------------------------------------
  expect "program: tri proved by induction" "proved(induction)" ["program", "examples/sequences.pl", "tri/2"]
  expect "program: tri formula" "formula: tri/2 at position i = (i + i * i) // 2" ["program", "examples/sequences.pl", "tri/2"]
  expect "program: pow2 proved" "proved(induction)" ["program", "examples/sequences.pl", "pow2/2"]
  expect "program: sumsq proved (cubic)" "proved(induction)" ["program", "examples/sequences.pl", "sumsq/2"]
  expect "program: grow proved (a b^n + c)" "proved(induction)" ["program", "examples/sequences.pl", "grow/2"]
  expect "program: odd has an inverse" "inverse: odd__inverse(V, N)" ["program", "examples/sequences.pl", "odd/2"]
  expect "program: sq only verified" "verified_on(" ["program", "examples/sequences.pl", "sq/2", "--domain", "0..20"]
  expect "program: fib has no formula" "no_formula" ["program", "examples/sequences.pl", "fib/2"]
  expect "program: loops replaced" "splice-index loops: 1" ["program", "examples/sequences.pl", "tri/2"]

  _ <- runP "./build/hs/algebraplop2" ["program", "examples/sequences.pl", "tri/2", "-o", "build/tri.pl"]
  expect "proof-check: accepted from files" "proof accepted" ["proof-check", "examples/sequences.pl", "build/tri.pl", "build/tri.pl.proof"]
  tri <- readFile "build/tri.pl"
  triProof <- readFile "build/tri.pl.proof"
  writeFile "build/tri_bad.pl" (replaceFirst "// 2" "// 3" tri)
  writeFile "build/tri_bad.proof" (replaceFirst "// 2" "// 3" triProof)
  expect "proof-check: a wrong formula is rejected" "proof rejected" ["proof-check", "examples/sequences.pl", "build/tri_bad.pl", "build/tri_bad.proof"]
  writeFile "build/tri_bad2.proof" (replaceFirst "m([1], 1 / 2)" "m([1], 3 / 2)" triProof)
  expect "proof-check: a wrong formula term is rejected" "proof rejected" ["proof-check", "examples/sequences.pl", "build/tri.pl", "build/tri_bad2.proof"]
  src <- readFile "examples/sequences.pl"
  writeFile "build/other.pl" (replaceFirst "T is T1 + N." "T is T1 + N + 1." src)
  expect "proof-check: another source is rejected" "proof rejected" ["proof-check", "build/other.pl", "build/tri.pl", "build/tri.pl.proof"]
  expectD2 "detlog2 runs the formula" "V = 55." ["run", "build/tri.pl", "tri__formula(10, V)"]
  expectD2 "detlog2 runs the splice-index loop" "Ts = [1, 3, 6, 10]." ["run", "build/tri.pl", "tris(1, 4, Ts)"]
  expectD2 "the formula keeps the domain" "false." ["run", "build/tri.pl", "tri__formula(-1, V)"]
  _ <- runP "./build/hs/algebraplop2" ["program", "examples/sequences.pl", "odd/2", "-o", "build/odd.pl"]
  expectD2 "detlog2 runs the inverse" "N = 4." ["run", "build/odd.pl", "odd__inverse(9, N)"]
  expectD2 "inverse fails off the image" "false." ["run", "build/odd.pl", "odd__inverse(8, N)"]
  expect "proof-check: odd" "proof accepted" ["proof-check", "examples/sequences.pl", "build/odd.pl", "build/odd.pl.proof"]

  swipl <- findExecutable "swipl"
  mnns <- lookupEnv "MNNS_DIR"
  case (swipl, mnns) of
    (Just _, Just dir) -> expect "mnns AlgebraPLOp agrees" "mnns AlgebraPLOp: formula(linear(3,1)" ["samples", "1,4,7,10,13", "--mnns", dir]
    _ -> putStrLn "SKIP mnns comparison"

  n <- readIORef fails
  putStrLn ""
  if n == 0 then putStrLn "all CLI tests passed" else do
    putStrLn (show n ++ " CLI test(s) failed")
    exitWith (ExitFailure 1)

replaceFirst :: String -> String -> String -> String
replaceFirst old new = go
  where
    go [] = []
    go s@(c : cs)
      | take (length old) s == old = new ++ drop (length old) s
      | otherwise = c : go cs
