import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Interval.Set.Instances
import Mathlib.Data.Real.Basic
import Mathlib.Topology.UnitInterval
open unitInterval



structure Tnorm where
    mul : I → I → I
    mul_assoc : ∀ p q r : I, mul (mul p q) r = mul p (mul q r)
    mul_comm : ∀ p q : I, mul p q = mul q p
    mul_one : ∀ p : I, mul p 1 = p
    mul_le_mul_left : ∀ p q : I, p ≤ q → ∀ r : I, mul r p ≤ mul r q

section namespace Tnorm

variable {T : Tnorm}


def IsIsomorphism (φ : I → I) := (Function.Bijective φ) ∧ (∀ p q : I, p ≤ q → φ p ≤ φ q)
def IsIsomorphismBetween (T₁ T₂ : Tnorm) (φ : I → I) :=
    (IsIsomorphism φ) ∧ (∀ p q : I, φ (T₁.mul p q) = T₂.mul (φ p) (φ q) )
def Isomorphic (T₁ T₂ : Tnorm) := ∃ φ : I → I, IsIsomorphismBetween T₁ T₂ φ


theorem mul_le_mul_right : ∀ p q : I, p ≤ q → ∀ r : I, T.mul p r ≤ T.mul q r := by
    intro p q
    intro h
    intro r
    nth_rw 1 [mul_comm]
    nth_rw 2 [mul_comm]
    apply mul_le_mul_left
    exact h
theorem mul_le_mul : ∀ p q r s : I , p ≤ q → r ≤ s → T.mul p r ≤ T.mul q s := by
    intro p q r s
    intro h
    intro h2
    calc T.mul p r
        _ ≤ T.mul q r := by apply mul_le_mul_right; exact h
        _ ≤ T.mul q s := by apply mul_le_mul_left; exact h2

@[simp] theorem mul_one' : ∀ p : I, T.mul p 1 = p := by exact T.mul_one
@[simp]
theorem one_mul : ∀ p : I, T.mul 1 p = p := by
    intro p
    rw[mul_comm]
    apply T.mul_one p

@[simp]
theorem zero_mul (p : I) : T.mul 0 p = 0 := by
  rw [← le_zero_iff]
  nth_rw 2 [← T.mul_one 0]
  apply T.mul_le_mul_left
  exact le_one p

@[simp]
theorem mul_zero (p : I) : T.mul p 0 = 0 := by
    rw[T.mul_comm]
    simp

theorem mul_self_le_self (p : I) : T.mul p p ≤ p := by
    nth_rw 3 [← T.one_mul p]
    apply T.mul_le_mul_right
    exact le_one p


/-instance mon (T : Tnorm) : OrderedCommMonoid I where
    mul := T.mul
    mul_assoc := T.mul_assoc
    mul_one := T.mul_one
    one_mul := T.one_mul
    mul_comm := T.mul_comm
    mul_le_mul_left := T.mul_le_mul_left-/


def npowRec (T : Tnorm) : ℕ → I → I
  | 0, _ => 1
  | n + 1, p => T.mul p (T.npowRec n p)

protected def npow (T : Tnorm) : ℕ → I → I := npowRec T

@[simp] theorem npow_zero (p : I) : T.npow 0 p = 1 := by rfl

theorem npow_succ (n : ℕ) (p : I) : T.npow (n+1) p = T.mul p (T.npow n p) := by rfl

@[simp] theorem npow_one (p : I) : T.npow 1 p = p := by rw [npow_succ]; simp

theorem npow_add (n m : ℕ) (p : I) : T.mul (T.npow n p) (T.npow m p) = T.npow (n+m) p := by
    induction' m with m ih
    simp

    rw [T.npow_succ, T.mul_comm, T.mul_assoc]
    nth_rw 2 [T.mul_comm]
    rw [ih, ← T.npow_succ, add_assoc]

theorem npow_le_self (n m : ℕ) (p : I) : n ≤ m → T.npow m p ≤ T.npow n p := by
    intro h
    induction' m with m ih
    apply Nat.eq_zero_of_le_zero at h
    rw [h]

    by_cases hnm : n=m+1
    rw [hnm]

    apply Nat.lt_of_le_of_ne h at hnm
    apply Nat.le_of_lt_succ at hnm
    apply ih at hnm
    calc T.npow (m+1) p
        _ = T.mul p (T.npow m p) := by rfl
        _ ≤ T.mul 1 (T.npow m p) := by apply T.mul_le_mul_right; exact le_one p
        _ = T.npow m p := by rw [T.one_mul]
        _ ≤ T.npow n p := by exact hnm


theorem npow_le (n : ℕ) (p q : I) : p ≤ q → T.npow n p ≤ T.npow n q := by
    intro h
    induction' n with n ih
    rw [npow_zero, npow_zero];

    apply T.mul_le_mul
    exact h
    exact ih

end Tnorm
