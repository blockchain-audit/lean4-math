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
