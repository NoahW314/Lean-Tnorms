import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Examples

import Mathlib.Topology.UnitInterval

open unitInterval


/- Major theorems about the structure of Tnorms that require representation approaches
  (using pseudo-inverses or generators or something like that)
-/

theorem nilpt_or_strict_of_cont_arch (T : Tnorm) : IsArchimedean T → Continuous T.mul → (IsNilpotent T ∨ IsStrict T) := by
  sorry

theorem luk_iso_of_nilpt (T : Tnorm) : IsNilpotent T → Tnorm.Isomorphic Tnorm.LukTnorm.toTnorm T := by
  sorry
