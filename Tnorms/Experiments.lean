import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Interval.Set.Instances
import Mathlib.Data.Real.Basic
import Mathlib.Topology.UnitInterval

open unitInterval


def Tnorm := OrderedCommMonoid I

section namespace Tnorm

variable {T : Tnorm}

theorem zero_mul (p : I) : T.mul 0 p = 0 := by
  rw [← le_zero_iff]
  nth_rw 2 [← T.mul_one 0]

  --have h : T.mul 0 p = T.hMul 0 p := by rfl
  --rw [h]
  have h : T.mul p 0 = T.toMul. p 0 := by
    unfold HMul.hMul instHMul
    simp

  /-have h : T.mul p q = T.mul
  unfold HMul.hMul instHMul
  simp

  have h : T.toMonoid.mul 0 p = Mul.mul 0 1 := by sorry-/


  --apply T.mul_le_mul_left
  --exact le_one p

end Tnorm
