import Tnorms.Defs
import Tnorms.LeftContinuity


section namespace FuzzyLogic

noncomputable
def Timp (T : Tnorm) (p q : I) := sSup (Subtype.val '' {r : I | T.mul p r ≤ q})
theorem Timp_mem (T : Tnorm) (p q : I) : (Timp T p q) ∈ I := by
    simp
    have h2 : Timp T p q = sSup (Subtype.val '' {r : I | T.mul p r ≤ q}) := by rfl
    constructor

    rw [h2]
    refine Real.sSup_nonneg' ?_
    use 0
    constructor
    simp
    rfl


    rw [h2]
    refine Real.sSup_le ?_ ?_
    intro x hx
    simp at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y1, y2⟩ := y
    exact y2
    simp

end FuzzyLogic

structure FuzzyLogic (T : Tnorm) where
    and : I → I → I := T.mul
    imp : I → I → I := fun p q => ⟨FuzzyLogic.Timp T p q, FuzzyLogic.Timp_mem T p q⟩
    and_def : ∀ p q : I, and p q = T.mul p q
    imp_def : ∀ p q : I, imp p q = ⟨FuzzyLogic.Timp T p q, FuzzyLogic.Timp_mem T p q⟩


section namespace FuzzyLogic

variable {T : Tnorm}
variable {L : FuzzyLogic T}

@[simp]
lemma imp_zero (p : I) : L.imp 0 p = (1 : ℝ) := by
    rw [L.imp_def]
    unfold Timp
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
    unfold Timp
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

lemma max_del_mem {p : I} {δ : ℝ} (h : δ > 0) : (max 0 (p - (δ/2))) ∈ I := by
    simp
    calc p.1
    _ ≤ 1 := by exact le_one p
    _ ≤ 1+(δ/2) := by refine le_add_of_le_of_nonneg ?_ ?_; rfl; apply le_of_lt; apply half_pos; exact h

lemma and_imp {T : LeftContinuousTnorm} {L : FuzzyLogic T.toTnorm} (p q : I) : T.mul p (L.imp p q) ≤ q.1 := by
    rw [L.imp_def]
    unfold Timp

    let s : I := ⟨sSup (Subtype.val '' {r | T.mul p r ≤ q}), Timp_mem T.toTnorm p q⟩
    let left_mul_real := fun r ↦ Subtype.val (T.mul p r)

    have h : T.mul p s ≤ sSup (left_mul_real '' {r | T.mul p r ≤ q}) := by
        by_cases hs : s = 0
        simp [hs]
        refine Real.sSup_nonneg ?_
        intro x hx
        simp at hx
        obtain ⟨a, haI, hamul, hareal⟩ := hx
        rw [← hareal]
        unfold left_mul_real
        exact nonneg (T.mul p ⟨a, haI⟩)

        have hs : s > 0 := by exact unitInterval.pos_iff_ne_zero.mpr hs
        refine (Real.le_sSup_iff ?_ ?_).mpr ?_
        apply bddAbove_def.mpr
        use 1
        simp
        intro y x hxI hmul hmr
        unfold left_mul_real at hmr
        rw [← hmr]
        exact le_one (T.mul p ⟨x, hxI⟩)
        simp
        use 0
        simp


        intro ε he
        have he : -ε > 0 := by exact Left.neg_pos_iff.mpr he
        apply T.left_cont_x s p (-ε) at he
        obtain ⟨δ, hdp, hd⟩ := he
        let r : I := ⟨max 0 (s - (δ/2)), max_del_mem hdp⟩
        have rsd : s - δ < r := by
            unfold r
            simp
            right
            exact hdp
        have rs : r.1 < s.1 := by
            unfold r
            simp
            constructor
            exact hs
            exact hdp
        have rs2 : r.1 ≤ s.1 := by exact le_of_lt rs

        specialize hd r rsd rs2
        use (T.mul p r)
        simp
        constructor
        use r
        simp
        constructor


        have hx : ∃ x ∈ (Subtype.val '' {r | T.mul p r ≤ q}), r < x := by
            refine (lt_csSup_iff ?_ ?_).mp rs
            apply bddAbove_def.mpr
            use 1
            intro y hy
            simp at hy
            obtain ⟨hyI, hymul⟩ := hy
            exact hyI.right

            use 0
            simp
        obtain ⟨x, hx, hxr⟩ := hx
        simp at hx
        obtain ⟨hxI, hxmul⟩ := hx
        apply le_of_lt at hxr
        calc T.mul p r
            _ ≤ T.mul p ⟨x, hxI⟩ := by exact T.mul_le_mul_left r ⟨x, hxI⟩ hxr p
            _ ≤ q := by exact hxmul


        constructor
        constructor
        exact nonneg r
        exact le_one r
        unfold left_mul_real
        simp

        rw [← abs_neg] at hd
        simp at hd
        apply lt_of_abs_lt at hd
        rw [T.mul_comm] at hd
        nth_rw 2 [T.mul_comm] at hd
        linarith


    apply le_trans h
    refine Real.sSup_le ?_ ?_

    intro x hx
    simp at hx
    obtain ⟨a, haI, hamul, hareal⟩ := hx
    unfold left_mul_real at hareal
    rw [← hareal]
    exact_mod_cast hamul

    exact nonneg q


lemma le_imp_iff_and_le {T : LeftContinuousTnorm} (L : FuzzyLogic T.toTnorm) (p q r : I) : T.mul r p ≤ q ↔ r ≤ L.imp p q := by
    constructor
    intro h
    rw [L.imp_def]
    unfold Timp
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
