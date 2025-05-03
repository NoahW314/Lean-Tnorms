import Tnorms.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Sequences
open unitInterval



structure LeftContinuousTnorm extends Tnorm where
    left_cont_x : ∀ p q : I, ∀ ε > 0, ∃ δ > 0, ∀ r : I, p.1-δ < r → r ≤ p → |(mul r q).1 - mul p q| < ε
--structure ContinuousTnorm extends LeftContinuousTnorm where


def IsLeftContinuousTnorm (T : Tnorm) := ∀ p q : I, ∀ ε > 0, ∃ δ > 0,
  ∀ r : I, p.1-δ < r → r ≤ p → |(T.mul r q).1 - (T.mul p q)| < ε
def IsRightContinuousTnorm (T : Tnorm) := ∀ p q : I, ∀ ε > 0, ∃ δ > 0,
  ∀ r : I, p.1 ≤ r → r < p.1+δ → |(T.mul r q).1 - (T.mul p q)| < ε

lemma left_cont_is_left_cont (T : LeftContinuousTnorm) : IsLeftContinuousTnorm T.toTnorm := by exact T.left_cont_x
