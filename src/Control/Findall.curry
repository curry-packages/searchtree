------------------------------------------------------------------------------
--- Library with some operations for encapsulating search.
--- Note that some of these operations are not fully declarative,
--- i.e., the results depend on the order of evaluation and program rules.
--- There are newer and better approaches the encapsulate search,
--- in particular, set functions (see module `SetFunctions`),
--- which should be used.
---
--- In previous versions of PAKCS, some of these operations were part of
--- the standard prelude. We keep them in this separate module
--- in order to support a more portable standard prelude.
---
--- @author Michael Hanus
--- @version December 2018
------------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# OPTIONS_CYMAKE -Wno-incomplete-patterns #-}

module Control.Findall
  ( getAllValues, getSomeValue
  , allValues, someValue, oneValue
  , allSolutions, someSolution
  , isFail
#ifdef __PAKCS__
  , try, inject, solveAll, once, best
  , findall, findfirst, browse, browseList, unpack
  , rewriteAll, rewriteSome
#endif
  ) where

#ifdef __PAKCS__
#else
import qualified Control.SearchTree as ST
#endif

--- Gets all values of an expression (currently, via an incomplete
--- depth-first strategy). Conceptually, all values are computed
--- on a copy of the expression, i.e., the evaluation of the expression
--- does not share any results. In PAKCS, the evaluation suspends
--- as long as the expression contains unbound variables.
--- Similar to Prolog's findall.
getAllValues :: a -> IO [a]
getAllValues e = return (allValues e)

--- Gets a value of an expression (currently, via an incomplete
--- depth-first strategy). The expression must have a value, otherwise
--- the computation fails. Conceptually, the value is computed on a copy
--- of the expression, i.e., the evaluation of the expression does not share
--- any results. In PAKCS, the evaluation suspends as long as the expression
--- contains unbound variables.
getSomeValue :: a -> IO a
getSomeValue e = return (someValue e)

--- Returns all values of an expression (currently, via an incomplete
--- depth-first strategy). Conceptually, all values are computed on a copy
--- of the expression, i.e., the evaluation of the expression does not share
--- any results. In PAKCS, the evaluation suspends as long as the expression
--- contains unbound variables.
---
--- Note that this operation is not purely declarative since the ordering
--- of the computed values depends on the ordering of the program rules.
allValues :: a -> [a]
#ifdef __PAKCS__
allValues external
#else
allValues e = ST.allValuesDFS (ST.someSearchTree e)
#endif

--- Returns some value for an expression (currently, via an incomplete
--- depth-first strategy). If the expression has no value, the
--- computation fails. Conceptually, the value is computed on a copy
--- of the expression, i.e., the evaluation of the expression does not share
--- any results. In PAKCS, the evaluation suspends as long as the expression
--- contains unbound variables.
---
--- Note that this operation is not purely declarative since
--- the computed value depends on the ordering of the program rules.
--- Thus, this operation should be used only if the expression
--- has a single value.
someValue :: a -> a
#ifdef __PAKCS__
someValue external
#else
someValue = ST.someValueWith ST.dfsStrategy
#endif

--- Returns just one value for an expression (currently, via an incomplete
--- depth-first strategy). If the expression has no value, `Nothing`
--- is returned. Conceptually, the value is computed on a copy
--- of the expression, i.e., the evaluation of the expression does not share
--- any results. In PAKCS, the evaluation suspends as long as the expression
--- contains unbound variables.
---
--- Note that this operation is not purely declarative since
--- the computed value depends on the ordering of the program rules.
--- Thus, this operation should be used only if the expression
--- has a single value.
oneValue :: a -> Maybe a
#ifdef __PAKCS__
oneValue external
#else
oneValue x =
  let vals = ST.allValuesWith ST.dfsStrategy (ST.someSearchTree x)
  in (if null vals then Nothing else Just (head vals))
#endif

--- Returns all values satisfying a predicate, i.e., all arguments such that
--- the predicate applied to the argument can be evaluated to `True`
--- (currently, via an incomplete depth-first strategy).
--- In PAKCS, the evaluation suspends as long as the predicate expression
--- contains unbound variables.
---
--- Note that this operation is not purely declarative since the ordering
--- of the computed values depends on the ordering of the program rules.
allSolutions :: (a->Bool) -> [a]
#ifdef __PAKCS__
allSolutions p = findall (\x -> p x =:= True)
#else
allSolutions p = allValues (let x free in p x &> x)
#endif

--- Returns some values satisfying a predicate, i.e., some argument such that
--- the predicate applied to the argument can be evaluated to `True`
--- (currently, via an incomplete depth-first strategy).
--- If there is no value satisfying the predicate, the computation fails.
---
--- Note that this operation is not purely declarative since the ordering
--- of the computed values depends on the ordering of the program rules.
--- Thus, this operation should be used only if the
--- predicate has a single solution.
someSolution :: (a->Bool) -> a
#ifdef __PAKCS__
someSolution p = findfirst (\x -> p x =:= True)
#else
someSolution p = someValue (let x free in p x &> x)
#endif

--- Does the computation of the argument to a head-normal form fail?
--- Conceptually, the argument is evaluated on a copy, i.e.,
--- even if the computation does not fail, it has not been evaluated.
isFail :: a -> Bool
#ifdef __PAKCS__
isFail external
#else
isFail x = null (allValues (x `seq` ()))
#endif

#ifdef __PAKCS__
------------------------------------------------------------------------------
--- Basic search control operator.
try     :: (a -> Bool) -> [a -> Bool]
try external

--- Inject operator which adds the application of the unary
--- procedure p to the search variable to the search goal
--- taken from Oz. p x comes before g x to enable a test+generate
--- form in a sequential implementation.
inject  :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
inject g p = \x -> p x & g x

--- Computes all solutions via a a depth-first strategy.
--
-- Works as the following algorithm:
--
-- solveAll g = evalResult (try g)
--         where
--           evalResult []      = []
--           evalResult [s]     = [s]
--           evalResult (a:b:c) = concatMap solveAll (a:b:c)
--
-- The following solveAll algorithm is faster.
-- For comparison we have solveAll2, which implements the above algorithm.

solveAll     :: (a -> Bool) -> [a -> Bool]
solveAll g = evalall (try g)
  where
    evalall []      = []
    evalall [a]     = [a]
    evalall (a:b:c) = evalall3 (try a) (b:c)

    evalall2 []    = []
    evalall2 (a:b) = evalall3 (try a) b

    evalall3 []      b  = evalall2 b
    evalall3 [l]     b  = l : evalall2 b
    evalall3 (c:d:e) b  = evalall3 (try c) (d:e ++b)


solveAll2  :: (a -> Bool) -> [a -> Bool]
solveAll2 g = evalResult (try g)
        where
          evalResult []      = []
          evalResult [s]     = [s]
          evalResult (a:b:c) = concatMap solveAll2 (a:b:c)


--- Gets the first solution via a depth-first strategy.
once :: (a -> Bool) -> (a -> Bool)
once g = head (solveAll g)


--- Gets the best solution via a depth-first strategy according to
--- a specified operator that can always take a decision which
--- of two solutions is better.
--- In general, the comparison operation should be rigid in its arguments!
best           :: (a -> Bool) -> (a -> a -> Bool) -> [a -> Bool]
best g cmp = bestHelp [] (try g) []
 where
   bestHelp [] []     curbest = curbest
   bestHelp [] (y:ys) curbest = evalY (try (constrain y curbest)) ys curbest
   bestHelp (x:xs) ys curbest = evalX (try x) xs ys curbest

   evalY []        ys curbest = bestHelp [] ys curbest
   evalY [newbest] ys _       = bestHelp [] ys [newbest]
   evalY (c:d:xs)  ys curbest = bestHelp (c:d:xs) ys curbest

   evalX []        xs ys curbest = bestHelp xs ys curbest
   evalX [newbest] xs ys _       = bestHelp [] (xs++ys) [newbest]
   evalX (c:d:e)   xs ys curbest = bestHelp ((c:d:e)++xs) ys curbest

   constrain y []        = y
   constrain y [curbest] =
      inject y (\v -> let w free in curbest w & cmp v w  =:= True)


--- Gets all solutions via a depth-first strategy and unpack
--- the values from the lambda-abstractions.
--- Similar to Prolog's findall.
findall :: (a -> Bool) -> [a]
findall external


--- Gets the first solution via a depth-first strategy
--- and unpack the values from the search goals.
findfirst :: (a -> Bool) -> a
findfirst external

--- Shows the solution of a solved constraint.
browse  :: Show a => (a -> Bool) -> IO ()
browse g = putStr (show (unpack g))

--- Unpacks solutions from a list of lambda abstractions and write
--- them to the screen.
browseList :: Show a => [a -> Bool] -> IO ()
browseList []     = done
browseList (g:gs) = browse g >> putChar '\n' >> browseList gs


--- Unpacks a solution's value from a (solved) search goal.
unpack  :: (a -> Bool) -> a
unpack g | g x = x where x free

--- Gets all values computable by term rewriting.
--- In contrast to `findall`, this operation does not wait
--- until all "outside" variables are bound to values,
--- but it returns all values computable by term rewriting
--- and ignores all computations that requires bindings for outside variables.
rewriteAll :: a -> [a]
rewriteAll external

--- Similarly to 'rewriteAll' but returns only some value computable
--- by term rewriting. Returns `Nothing` if there is no such value.
rewriteSome :: a -> Maybe a
rewriteSome external
#endif
