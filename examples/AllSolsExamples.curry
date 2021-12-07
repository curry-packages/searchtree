-- Some examples for the use of the module Control.AllSolutions
{-# OPTIONS_FRONTEND -Wno-overlapping #-}

import Control.AllSolutions

-- The famous non-deterministic function:
coin :: Int
coin = 0
coin = 1

-- Principal use of getAllSolutions:
all1 :: IO ()
all1 = getAllSolutions (=:=(coin+coin)) >>= print

-- This example shows that no sharing is performed across encapsulated search:
all2 :: IO ()
all2 = let cc = coin+coin in 
  getAllSolutions (=:=cc) >>= print >>
  getAllSolutions (=:=cc) >>= print

-- Example for getOneValue:
first1 :: IO ()
first1 = getOneValue (coin+coin) >>= print


-- An application of getAllFailures:
--
-- Place n queens on a chessboard so that no queen can capture another queen:
-- (this solution is due to Sergio Antoy)

queens :: Int -> IO [[Int]]
queens n = getAllFailures (permute [1..n]) capture
 where
  capture y = let l1,l2,l3,y1,y2 free in
    l1 ++ [y1] ++ l2 ++ [y2] ++ l3 =:= y & abs (y1-y2) =:= length l2 + 1

  permute []     = []
  permute (x:xs) = ndinsert (permute xs)
   where ndinsert ys     = x : ys
         ndinsert (y:ys) = y : ndinsert ys

