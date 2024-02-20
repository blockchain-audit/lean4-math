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


-- method hoare2A(x: int) returns (y: int)
-- requires x < 18
-- ensures 0 <= y {
--   y := 18 - x;
-- }
-- translate this dafny code to lean4, incluidng the pre and pos conditions

-- def hoare2A (x :  ℕ) (h : x <  18) :  ℕ :=
--   let y :=  18 - x in
--   have h' :  0  ≤ y, from nat.sub_le_self  18 x
--   y


def myArray : Array ℕ  := #[] -- An empty array of natural numbers

def myArrayWithElements : Array ℕ  := #[1,  2,  3] -- An array with elements

def sumArray (a : Array Nat) : Nat :=
  a.foldl (λ acc n => acc + n)  0 -- Summing the elements of an array

#eval sumArray myArrayWithElements -- Evaluates to  6
