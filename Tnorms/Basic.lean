import Tnorms.Defs
import Mathlib.Topology.UnitInterval
open unitInterval

namespace Tnorm

variable {T : Tnorm}

theorem mul_le_mul_right : ∀ p q : I, p ≤ q → ∀ r : I, T.mul p r ≤ T.mul q r := by
    intro p q h r
    nth_rw 1 [mul_comm]
    nth_rw 2 [mul_comm]
    apply mul_le_mul_left
    exact h
theorem mul_le_mul : ∀ p q r s : I , p ≤ q → r ≤ s → T.mul p r ≤ T.mul q s := by
    intro p q r s h h2
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

theorem mul_le_left (p q : I) : T.mul p q ≤ p := by
    nth_rw 2 [← T.mul_one' p]
    apply T.mul_le_mul_left
    exact le_one q
theorem mul_le_right (p q : I) : T.mul p q ≤ q := by rw [T.mul_comm]; exact mul_le_left q p
theorem mul_le_min (p q : I) : T.mul p q ≤ p ⊓ q := le_inf (mul_le_left p q) (mul_le_right p q)

theorem mul_self_le_self (p : I) : T.mul p p ≤ p := mul_le_left p p


@[simp] theorem npow_zero (p : I) : T.npow 0 p = 1 := by rfl

theorem npow_succ (n : ℕ) (p : I) : T.npow (n+1) p = T.mul p (T.npow n p) := by rfl

@[simp] theorem npow_one (p : I) : T.npow 1 p = p := by rw [npow_succ]; simp

@[simp] theorem npow_two (p : I) : T.npow 2 p = T.mul p p := by rw[npow_succ, npow_one]

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

theorem npow_mul (n m : ℕ) (p : I) : T.npow m (T.npow n p) = T.npow (m*n) p := by
    induction' m with m ih
    rw [Nat.zero_mul, npow_zero, npow_zero]
    rw [← npow_add, npow_one, Nat.succ_mul, ← npow_add, ih]

lemma npow_I_one (T : Tnorm) (n : ℕ) : T.npow n 1 = 1 := by
  induction' n with n ih
  exact T.npow_zero 1
  rw [T.npow_succ, T.one_mul, ih]
