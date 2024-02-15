import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import MIL.Common
import Lean

open Nat
open Lean

-- These are pieces of data.
#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f

-- These are propositions, of type `Prop`.
#check 2 + 2 = 4
#check 4 + 4 = 9
#eval 4 + 4 = 9
#eval 10 + 10 = 20

def  fac := ∀ x y : ℕ, 2*(x + y) = 2*x + 2*y
#check fac

-- as fac is a Prop, we can't evaluate like: eval fac 3 2

def fac1 (n: ℕ ) : ℕ :=
  match n with
  | 0 => 1
  | (Nat.succ m) => n * fac1 m


#eval fac1 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

def isPrime (n :  ℕ) : Prop :=
   2  ≤ n  ∧  ∀ m :  ℕ, m  ≤ n → m  ≠  1 → m  ≠ n →  ¬ (n % m =  0)

#check isPrime


#check FermatLastTheorem

-- These are proofs of propositions.
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard

-- Here are some proofs.
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say m and n are natural numbers, and assume n=2*k.
  rintro m n ⟨k, hk⟩
  -- We need to prove m*n is twice a natural number. Let's show it's twice m*k.
  use m * k
  -- Substitute for n,
  rw [hk]
  -- and now it's obvious.
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
