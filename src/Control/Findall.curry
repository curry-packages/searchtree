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
--- @version June 2021
------------------------------------------------------------------------------
{-# LANGUAGE CPP #-}

module Control.Findall
  ( getAllValues, getSomeValue
  , allValues, someValue, oneValue
  , allSolutions, someSolution, oneSolution
  , isFail
#ifdef __PAKCS__
  , rewriteAll, rewriteSome
#endif
  ) where

#ifdef __KICS2__
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
#ifdef __KICS2__
allValues e = ST.allValuesDFS (ST.someSearchTree e)
#else
allValues external
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
#ifdef __KICS2__
someValue = ST.someValueWith ST.dfsStrategy
#else
someValue external
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
#ifdef __KICS2__
oneValue x =
  let vals = ST.allValuesWith ST.dfsStrategy (ST.someSearchTree x)
  in (if null vals then Nothing else Just (head vals))
#else
oneValue external
#endif

--- Returns all values satisfying a predicate, i.e., all arguments such that
--- the predicate applied to the argument can be evaluated to `True`
--- (currently, via an incomplete depth-first strategy).
--- In PAKCS, the evaluation suspends as long as the predicate expression
--- contains unbound variables.
---
--- Note that this operation is not purely declarative since the ordering
--- of the computed values depends on the ordering of the program rules.
allSolutions :: Data a => (a -> Bool) -> [a]
allSolutions p = allValues (invertPred p)

--- Returns some value satisfying a predicate, i.e., some argument such that
--- the predicate applied to the argument can be evaluated to `True`
--- (currently, via an incomplete depth-first strategy).
--- If there is no value satisfying the predicate, the computation fails.
---
--- Note that this operation is not purely declarative since the ordering
--- of the computed values depends on the ordering of the program rules.
--- Thus, this operation should be used only if the
--- predicate has a single solution.
someSolution :: Data a => (a -> Bool) -> a
someSolution p = someValue (invertPred p)

--- Returns just one value satisfying a predicate.
--- If there is no such value, `Nothing` is returned
---
--- Note that this operation is not purely declarative since
--- the computed value depends on the ordering of the program rules.
--- Thus, this operation should be used only if the expression
--- has a single value.
oneSolution :: Data a => (a -> Bool) -> Maybe a
oneSolution p = oneValue (invertPred p)

-- Inverts a predicate, i.e., compute all values for which the predicate
-- succeeds.
invertPred :: Data a => (a -> Bool) -> a
invertPred p | p x = x where x free

--- Does the computation of the argument to a head-normal form fail?
--- Conceptually, the argument is evaluated on a copy, i.e.,
--- even if the computation does not fail, it has not been evaluated.
isFail :: a -> Bool
#ifdef __KICS2__
isFail x = null (allValues (x `seq` ()))
#else
isFail external
#endif

#ifdef __PAKCS__
------------------------------------------------------------------------------
--- Gets all values computable by term rewriting.
--- In contrast to `allValues`, this operation does not wait
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
