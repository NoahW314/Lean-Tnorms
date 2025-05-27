import Tnorms.Defs
import Tnorms.Basic
import Tnorms.LeftContinuity
import Mathlib.Topology.UnitInterval
open unitInterval

structure FuzzyLogic (T : Tnorm) where
    and : I → I → I := T.mul
    imp : I → I → I := fun p q => sSup ({r : I | T.mul p r ≤ q})
    and_def : ∀ p q : I, and p q = T.mul p q
    imp_def : ∀ p q : I, imp p q = sSup ({r : I | T.mul p r ≤ q})

section namespace FuzzyLogic

variable {T : Tnorm}
variable {L : FuzzyLogic T}

@[simp]
lemma imp_zero (p : I) : L.imp 0 p = (1 : ℝ) := by
    rw [L.imp_def]
    simp only [Tnorm.zero_mul, zero_le', Set.setOf_true, sSup_univ, Set.Icc.coe_top]

@[simp]
lemma imp_self (p : I) : L.imp p p = (1 : ℝ) := by
    rw [L.imp_def, Set.Icc.coe_eq_one]
    refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
    intro a ha; exact a.2.2

    intro w hw; use 1; constructor
    rw [Set.mem_setOf]
    exact T.mul_le_left p 1
    exact hw

lemma and_imp {T : LeftContinuousTnorm} {L : FuzzyLogic T.toTnorm} (p q : I) : T.mul p (L.imp p q) ≤ q.1 := by
    let S := {r | T.mul p r ≤ q}
    have h : T.mul p (L.imp p q) ≤ sSup (Set.range (fun (s : S) => T.mul s p)) := by
        rw [L.imp_def, T.mul_comm]
        rw [← left_cont_sup T S p]
    apply le_trans h
    apply sSup_le

    intro x hx
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_Icc] at hx
    obtain ⟨a, haI, haS, hamul⟩ := hx
    rw [← hamul]
    unfold S at haS; rw [Set.mem_setOf_eq] at haS
    rw [T.mul_comm]; exact haS


lemma le_imp_iff_and_le {T : LeftContinuousTnorm} (L : FuzzyLogic T.toTnorm) (p q r : I) : T.mul r p ≤ q ↔ r ≤ L.imp p q := by
    constructor; intro h
    rw [L.imp_def]
    apply le_sSup
    rw [Set.mem_setOf, T.mul_comm]; exact h

    intro h
    calc T.mul r p
        _ ≤ T.mul (L.imp p q) p := by apply T.mul_le_mul_right; exact h
        _ = T.mul p (L.imp p q) := by rw [T.mul_comm]
        _ ≤ q := by exact L.and_imp p q


end FuzzyLogic
