-- Some examples for search trees of the module Control.AllSolutions
{-# OPTIONS_FRONTEND -Wno-overlapping #-}

import Control.AllSolutions


-- Generate search tree of depth 0 (similar to getAllSolutions):
tree0 :: IO (SearchTree Int Int)
tree0 = getSearchTree [] (=:=(x+y))
        where
          x=coin
          y=coin
--> (Solutions [0,1,1,2])

-- Generate search tree of depth 1:
tree1 = getSearchTree [x+5] (=:=(x+y)) >>= print
        where
          x=coin
          y=coin 
--> (SearchBranch [(5,(Solutions [0,1])),(6,(Solutions [1,2]))])

-- Generate search tree of depth 2:
tree2 = getSearchTree [x,y] (=:=(x+y=:=1)) >>= print
        where
          x=coin
          y=coin  
--> (SearchBranch [(0,(SearchBranch [(0,(Solutions [])),
--                                   (1,(Solutions [True]))])),
--                 (1,(SearchBranch [(0,(Solutions [True])),
--                                   (1,(Solutions []))]))])

