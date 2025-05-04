import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Algebra
import Tnorms.Continuity
import Tnorms.LeftContinuity

/-
noncomputable
def rightLim (T : Tnorm) (p q : I) := sInf (Subtype.val '' ((Function.uncurry T.mul) '' {(r, s) : I × I | (p ≤ r ∧ q < s) ∨ (p < r ∧ q ≤ s)}))
lemma rightLimI {T : Tnorm} {p q : I} : rightLim T p q ∈ I := by sorry

noncomputable
def leftLim (T : Tnorm) (p q : I) := sInf (Subtype.val '' ((Function.uncurry T.mul) '' {(r, s) : I × I | (s ≤ p ∧ s < q) ∨ (r < p ∧ s ≤ q)}))
lemma leftLimI {T : Tnorm} {p q : I} : leftLim T p q ∈ I := by sorry

theorem right_cont_lim {T : Tnorm} (h : ∀ p q : I, rightLim T p q = T.mul p q) : IsRightContinuousTnorm T := by
  sorry

theorem left_cont_lim {T : Tnorm} (h : ∀ p q : I, leftLim T p q = T.mul p q) : IsLeftContinuousTnorm T := by
  sorry

theorem cont_of_left_right_cont {T : Tnorm} : IsLeftContinuousTnorm T → IsRightContinuousTnorm T → Continuous T.mul := by
  sorry

theorem right_cont_on_boundary (T : Tnorm) (p q : I) : (¬ IsNontrivial p ∨ ¬ IsNontrivial q) →
  rightLim T p q = T.mul p q := by
    sorry

theorem le_right_lim (T : Tnorm) (p q : I) : T.mul p q ≤ rightLim T p q := by
    sorry

theorem min_pow_arch (T : Tnorm) (h : IsArchimedean T) : ∀ p q : I, IsNontrivial p → IsNontrivial q →
  ∃ n : ℕ, T.npow (n+1) p ≤ q ∧ q < T.npow n p := by
    sorry

noncomputable
def limI (z : ℕ → I) (hz : ∀ n : ℕ, z n ≤ z (n+1)) := sSup (Subtype.val '' (Set.range z))
--theorem seq_T_inc (T : Tnorm) (z : ℕ → I)
--theorem left_cont_seq_lim (T : Tnorm) (z : ℕ → I) (hz : ∀ n : ℕ, z n ≤ z (n+1)) :
-/

theorem cont_of_left_cont_arch (T : LeftContinuousTnorm) : IsArchimedean T.toTnorm → T.Continuous := by
  intro h
  /-apply cont_of_left_right_cont
  exact left_cont_is_left_cont T
  apply right_cont_lim
  intro x y
  by_cases hnt : (¬ IsNontrivial x ∨ ¬ IsNontrivial y)
  exact right_cont_on_boundary T.toTnorm x y hnt

  push_neg at hnt
  by_contra hc
  push_neg at hc
  symm at hc
  apply lt_of_le_of_ne (le_right_lim T.toTnorm x y) at hc

  let z : ℕ → I := fun n => ⟨1-1/(n+2), by
      constructor
      simp
      refine inv_le_one_of_one_le₀ ?_
      linarith

      simp
      linarith
    ⟩
  have hznt : ∀ n : ℕ, IsNontrivial (z n) := by sorry
  let u : ℕ → ℕ := fun n => Classical.choose (min_pow_arch T.toTnorm h (z n) x (hznt n) hnt.1)
  let v : ℕ → ℕ := fun n => Classical.choose (min_pow_arch T.toTnorm h (z n) y (hznt n) hnt.2)

  have hnn2 : ∀ n : ℕ, T.npow ((u n) + (v n) + 2) (z n) ≤ T.mul x y := by sorry
  have hnn : ∀ n : ℕ, rightLim T.toTnorm x y ≤ T.npow ((u n) + (v n)) (z n) := by
      sorry

  have hnn22 : ∀ n : ℕ, T.mul (⟨rightLim T.toTnorm x y, rightLimI⟩) (T.mul (z n) (z n)) ≤  T.npow ((u n) + (v n) + 2) (z n) := by
      sorry
-/

  sorry
