import Tnorms.Defs
import Tnorms.Basic
import Tnorms.LeftContinuity
import Mathlib.Topology.UnitInterval
open unitInterval

structure FuzzyLogic (T : Tnorm) where
    and : I → I → I := T.mul
    imp : I → I → I := fun p q => ⟨sSup (Subtype.val '' {r : I | T.mul p r ≤ q}), sup_mem_I⟩
    and_def : ∀ p q : I, and p q = T.mul p q
    imp_def : ∀ p q : I, imp p q = ⟨sSup (Subtype.val '' {r : I | T.mul p r ≤ q}), sup_mem_I⟩

section namespace FuzzyLogic

variable {T : Tnorm}
variable {L : FuzzyLogic T}

@[simp]
lemma imp_zero (p : I) : L.imp 0 p = (1 : ℝ) := by
    rw [L.imp_def]
    refine csSup_eq_of_is_forall_le_of_forall_le_imp_ge ?_ ?_ ?_

    use 0
    simp

    intro a
    intro ha
    simp at ha
    exact ha.right

    intro b
    intro ha
    specialize ha 1
    simp at ha
    exact ha

@[simp]
lemma imp_self (p : I) : L.imp p p = (1 : ℝ) := by
    rw [L.imp_def]
    refine csSup_eq_of_is_forall_le_of_forall_le_imp_ge ?_ ?_ ?_

    use 0
    simp

    intro a
    intro ha
    simp at ha
    obtain ⟨b, hb⟩ := ha
    exact b.right

    intro b
    intro hb
    specialize hb 1
    apply hb
    simp

lemma and_imp {T : LeftContinuousTnorm} {L : FuzzyLogic T.toTnorm} (p q : I) : T.mul p (L.imp p q) ≤ q.1 := by
    let S := {r | T.mul p r ≤ q}

    have h : T.mul p (L.imp p q) ≤ sSup (Subtype.val '' Set.range (fun (s : S) => T.mul s p)) := by
        rw [L.imp_def, T.mul_comm]
        rw [← left_cont_sup T S p]

    apply le_trans h
    refine Real.sSup_le ?_ ?_

    intro x hx
    simp at hx
    obtain ⟨hxI, a, haI, hamul, hareal⟩ := hx
    apply Subtype.mk_le_mk.mp
    rw [← hareal]
    unfold S at hamul
    apply Set.mem_setOf_eq.mp at hamul
    rw [T.mul_comm]
    exact_mod_cast hamul
    exact nonneg q


lemma le_imp_iff_and_le {T : LeftContinuousTnorm} (L : FuzzyLogic T.toTnorm) (p q r : I) : T.mul r p ≤ q ↔ r ≤ L.imp p q := by
    constructor
    intro h
    rw [L.imp_def]
    have hr : r.1 ∈ Subtype.val '' {z | T.mul p z ≤ q} := by
        simp
        constructor
        exact r.2
        rw [T.mul_comm]
        exact h
    refine le_csSup ?_ hr

    apply bddAbove_def.mpr
    use 1
    intro y
    simp
    intro hy
    intro hymul
    exact hy.right

    intro h
    calc T.mul r p
        _ ≤ T.mul (L.imp p q) p := by apply T.mul_le_mul_right; exact h
        _ = T.mul p (L.imp p q) := by rw [T.mul_comm]
        _ ≤ q := by exact L.and_imp p q


end FuzzyLogic
