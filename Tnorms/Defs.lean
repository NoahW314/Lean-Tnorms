import Mathlib.Topology.UnitInterval
open unitInterval



structure Tnorm where
    mul : I → I → I
    mul_assoc : ∀ p q r : I, mul (mul p q) r = mul p (mul q r)
    mul_comm : ∀ p q : I, mul p q = mul q p
    mul_one : ∀ p : I, mul p 1 = p
    mul_le_mul_left : ∀ p q : I, p ≤ q → ∀ r : I, mul r p ≤ mul r q


section namespace Tnorm

def npowRec (T : Tnorm) : ℕ → I → I
  | 0, _ => 1
  | n + 1, p => T.mul p (T.npowRec n p)

protected def npow (T : Tnorm) : ℕ → I → I := npowRec T


def Isomorphism (φ : I → I) := (Function.Bijective φ) ∧ (Monotone φ)
def IsomorphismBetween (T₁ T₂ : Tnorm) (φ : I → I) :=
    (Isomorphism φ) ∧ (∀ p q : I, φ (T₁.mul p q) = T₂.mul (φ p) (φ q) )
def Isomorphic (T₁ T₂ : Tnorm) := ∃ φ : I → I, IsomorphismBetween T₁ T₂ φ


def LeftContinuous (T : Tnorm) := ∀ x y : ℕ → I, ∀ p q : I, Monotone x → Monotone y →
  Filter.Tendsto x Filter.atTop (nhds p)
  → Filter.Tendsto y Filter.atTop (nhds q)
  → Filter.Tendsto (fun n => T.mul (x n) (y n)) Filter.atTop (nhds (T.mul p q))
def RightContinuous (T : Tnorm) := ∀ x y : ℕ → I, ∀ p q : I, Antitone x → Antitone y →
  Filter.Tendsto x Filter.atTop (nhds p)
  → Filter.Tendsto y Filter.atTop (nhds q)
  → Filter.Tendsto (fun n => T.mul (x n) (y n)) Filter.atTop (nhds (T.mul p q))
def Continuous (T : Tnorm) :=  ∀ x y : ℕ → I, ∀ p q : I,
  Filter.Tendsto x Filter.atTop (nhds p)
  → Filter.Tendsto y Filter.atTop (nhds q)
  → Filter.Tendsto (fun n => T.mul (x n) (y n)) Filter.atTop (nhds (T.mul p q))

end Tnorm

structure LeftContinuousTnorm extends Tnorm where
    left_cont : toTnorm.LeftContinuous

structure RightContinuousTnorm extends Tnorm where
    right_cont : toTnorm.RightContinuous

structure ContinuousTnorm extends LeftContinuousTnorm, RightContinuousTnorm where
  cont : toTnorm.Continuous


section namespace Tnorm

theorem left_cont_of_cont (T : Tnorm) (h : T.Continuous) : T.LeftContinuous := by
    intro x y p q _ _ hx hy
    exact h x y p q hx hy
theorem right_cont_of_cont (T : Tnorm) (h : T.Continuous) : T.RightContinuous := by
    intro x y p q _ _ hx hy
    exact h x y p q hx hy

def toLeftContinuousTnorm (T : Tnorm) (h : T.LeftContinuous) := (⟨T, h⟩ : LeftContinuousTnorm)
def toRightContinuousTnorm (T : Tnorm) (h : T.RightContinuous) := (⟨T, h⟩ : RightContinuousTnorm)
def toContinuousTnorm (T : Tnorm) (h : T.Continuous) :=
    (⟨T.toLeftContinuousTnorm (T.left_cont_of_cont h), T.right_cont_of_cont h, h⟩ : ContinuousTnorm)

end Tnorm
