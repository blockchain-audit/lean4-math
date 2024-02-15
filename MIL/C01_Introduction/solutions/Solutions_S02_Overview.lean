import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import MIL.Common

open Nat





theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
fun hpq : p ∧ q =>
have hp : p := And.left hpq
have hq : q := And.right hpq
show q ∧ p from And.intro hq hp
-- There are no exercises in this section.



def gcd : (a : Nat) -> (b : Nat) -> (gas : Nat) -> Option Nat
| _, _, 0 => none -- out of gas
| a, 0, _ => some a
| a, b, (gas+1) => gcd b (a % b) gas


#eval gcd 50 100 5

/--Reynaud's first runtime bound on the number of steps in Euclid's algorithm.--/
theorem gcd_runtime_bound_Reynaud
  (a b fuel : Nat)
  (h : b < fuel)
  : (gcd a b fuel).isSome :=
  -- The details are left as an exercise to the reader,
  -- but should be similar to other proofs about
  -- Euclid's algorithm using strong induction.
  sorry
