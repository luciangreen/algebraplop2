-- | 200 inputs and the outputs they give, from real runs of algebraplop2.
--
--   runghc Build.hs ios        runs the 200 inputs and writes io/ios.txt
--   runghc Build.hs check-ios  runs them again and fails if any output changed
--
-- The inputs are made the same way every time (see 'cases').  Each output is
-- everything the command printed, with its exit code when that is not 0.
module Main (main) where

import Data.Char (isAlphaNum)
import Data.List (intercalate)
import System.Environment (getArgs, getEnvironment)
import System.Exit
import System.Process

title :: String
title = "algebraplop2"

binary :: FilePath
binary = "./build/hs/algebraplop2"

-- | Choose element i (from the case number k and a salt) of a list.
pick :: Int -> Int -> [a] -> a
pick k salt xs = xs !! ((k * (2 * salt + 1) + salt * 7) `mod` length xs)

-- | A list of length n from a pool, starting at a place set by k.
pickN :: Int -> Int -> Int -> [a] -> [a]
pickN k salt n xs = take n (drop ((k * (salt + 3)) `mod` length xs) (cycle xs))

showList' :: [Int] -> String
showList' xs = "[" ++ intercalate "," (map show xs) ++ "]"

pool :: [Int]
pool = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

-- | A sequence of the given kind: values at positions 0 .. n-1.
seqOf :: Int -> [Integer]
seqOf k =
  let n = 4 + k `mod` 6
      a = fromIntegral (k `mod` 7) - 2
      b = fromIntegral (k `mod` 5) + 1
      c = fromIntegral (k `mod` 3)
      is = [0 .. fromIntegral n - 1]
  in case k `mod` 7 of
       0 -> [ a * i + b | i <- is ]
       1 -> [ a * i * i + b * i + c | i <- is ]
       2 -> [ b * (c + 2) ^ i | i <- is ]
       3 -> [ (if even i then a * i else b * i + c) | i <- is ]
       4 -> [ fromIntegral (pick k (fromIntegral i) pool) | i <- is ]
       5 -> [ b * (c + 2) ^ i + a | i <- is ]
       _ -> [ i * i * i - a * i | i <- is ]

csv :: [Integer] -> String
csv = intercalate "," . map show

-- | The 200 inputs: (command arguments).
cases :: [[String]]
cases = [ caseFor k | k <- [1 .. 200] ]

caseFor :: Int -> [String]
caseFor k = case k `mod` 4 of
  0 -> ["program", "examples/sequences.pl", pick k 1 ["tri/2", "pow2/2", "odd/2", "sumsq/2", "grow/2", "sq/2", "fib/2"]
       , "--domain", show (k `mod` 3) ++ ".." ++ show (8 + k `mod` 9)]
  1 -> ["samples", unwords [ "[" ++ show i ++ "," ++ show j ++ "]-" ++ show (fromIntegral (k `mod` 5) * i + fromIntegral (k `mod` 3) * j + i * j * fromIntegral (k `mod` 2))
                           | i <- [0 .. 2 :: Integer], j <- [0 .. 2 :: Integer] ]]
  _ -> ["samples", csv (seqOf k)]

quoteArg :: String -> String
quoteArg a
  | all (\c -> isAlphaNum c || c `elem` "/._-") a && not (null a) = a
  | otherwise = "'" ++ concatMap (\c -> if c == '\'' then "'\\''" else [c]) a ++ "'"

runCase :: [(String, String)] -> [String] -> IO String
runCase env args = do
  (code, out, err) <- readCreateProcessWithExitCode ((proc binary args) { env = Just env }) ""
  let text = trimEnd (out ++ err)
      codeLine = case code of
        ExitSuccess -> ""
        ExitFailure n -> "\n(exit code " ++ show n ++ ")"
  return (text ++ codeLine)
  where
    trimEnd = reverse . dropWhile (`elem` " \n") . reverse

render :: [([String], String)] -> String
render results = unlines $
  (title ++ ": 200 inputs and outputs, from real runs (runghc Build.hs ios writes this file; "
     ++ "runghc Build.hs check-ios checks it).")
  : concat [ [ "", show i ++ ". " ++ unwords (title : map quoteArg args) ]
             ++ case lines out of
                  [] -> ["   => (no output)"]
                  (l : ls) -> ("   => " ++ l) : map ("      " ++) ls
           | (i, (args, out)) <- zip [1 :: Int ..] results ]

main :: IO ()
main = do
  mode <- getArgs
  env0 <- getEnvironment
  -- the same runs everywhere: no optional tools from the environment
  let env = filter ((`notElem` ["MNNS_DIR"]) . fst) env0
  outs <- mapM (runCase env) cases
  let text = render (zip cases outs)
  case mode of
    ["make"] -> writeFile "haskell/io/ios.txt" text >> putStrLn "wrote haskell/io/ios.txt (200 inputs and outputs)"
    ["check"] -> do
      old <- readFile "haskell/io/ios.txt"
      if length old == length text && old == text
        then putStrLn "All 200 inputs give the outputs in io/ios.txt."
        else do
          let diffs = [ (n, a, b) | (n, a, b) <- zip3 [1 :: Int ..] (lines old) (lines text), a /= b ]
          mapM_ (\(n, a, b) -> putStrLn ("line " ++ show n ++ ":\n  recorded: " ++ a ++ "\n  now:      " ++ b)) (take 20 diffs)
          putStrLn "Outputs differ from io/ios.txt. If the change is meant, run runghc Build.hs ios and commit io/ios.txt."
          exitWith (ExitFailure 1)
    _ -> putStrLn "usage: ios make | ios check" >> exitWith (ExitFailure 2)
