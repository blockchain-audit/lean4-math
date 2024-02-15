-- https://github.com/leanprover/lean4/blob/cade2021/doc/BoolExpr.lean
-- https://pp.ipd.kit.edu/uploads/publikationen/demoura21lean4.pdf
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import MIL.Common
import Std

open Std
open Lean
open Nat


-- Each category builds upon the previous one, incorporating more complex representations:
-- Natural numbers (1,2,3..)
-- are a subset of integers (-3, -2, -1, 0, 1, 2),
-- which are a subset of rational numbers (1/2, -3/4, 5.75),
-- which are a subset of real numbers (pi, sqrt(2), 0.01)



-- when a is true we already know the answer
-- when a is false, we depends on b, so if b
-- is false, the expression is false, else is true

def or1 (a b : Bool) :=
  match a with
  | true  => true
  | false => b

#check or1
#eval or1 true false
#eval or1 false false
