import Tnorms.Defs
import Tnorms.Continuity
import Tnorms.FuzzyLogic
import Mathlib.Topology.UnitInterval
open unitInterval

/-
define some basic T-norms:
  * the product T-norm
  * the Minimum (or Godel) T-norm
  * the Łukasiewicz T-norm
  * the drastic T-norm
  * the nilpotent minimum T-norm
-/
namespace Tnorm

def ProdTnorm' : Tnorm where
  mul p q := p*q
  mul_assoc := _root_.mul_assoc
  mul_comm := _root_.mul_comm
  mul_one := MulOneClass.mul_one
  mul_le_mul_left p q := by
    intro h r
    exact mul_le_mul_of_nonneg_left h r.2.1
theorem prod_cont : ProdTnorm'.Continuous := by
  apply (cont_def ProdTnorm').mpr
  have hprod : (Function.uncurry ProdTnorm'.mul) = (fun p : I×I => p.1*p.2) := by rfl
  rw [hprod]
  apply Continuous.subtype_mk ?_ ?_
  exact Continuous.mul (Continuous.fst' continuous_subtype_val) (Continuous.snd' continuous_subtype_val)
  intro x; exact unitInterval.mul_mem (Subtype.coe_prop x.1) (Subtype.coe_prop x.2)
def ProdTnorm : ContinuousTnorm := ProdTnorm'.toContinuousTnorm prod_cont
theorem prod_tnorm_def (p q : I) : ProdTnorm.mul p q = p*q := by rfl

def MinTnorm' : Tnorm where
    mul p q := min p q
    mul_assoc := min_assoc
    mul_comm := min_comm
    mul_one p := by
      simp only [inf_eq_left]
      exact le_one p
    mul_le_mul_left p q := by
      intro h r
      simp only [le_inf_iff, inf_le_left, inf_le_iff, true_and]; right; exact h
theorem min_cont : MinTnorm'.Continuous := (cont_def MinTnorm').mpr continuous_min
def MinTnorm : ContinuousTnorm := MinTnorm'.toContinuousTnorm min_cont
theorem min_tnorm_def (p q : I) : MinTnorm.mul p q = p ⊓ q := by rfl

lemma luk_max_mem_I (p q : I) : (max 0 (p.1+q-1)) ∈ I := by
  simp only [Set.mem_Icc, le_sup_left, sup_le_iff, zero_le_one, tsub_le_iff_right, true_and]
  calc p.1 + q
      _ = p+q := by rfl
      _ ≤ p+1 := by apply add_le_add_left; exact_mod_cast le_one q
      _ ≤ 1+1 := by apply add_le_add_right; exact_mod_cast le_one p
def LukTnorm' : Tnorm where
    mul p q := ⟨max 0 (p+q-1), luk_max_mem_I p q⟩
    mul_assoc p q r := by
        simp only [Subtype.mk.injEq]
        by_cases h : 0 ≤ p.1+q-1
        · apply sup_eq_right.mpr at h
          rw [h]

          by_cases h2 : 0 ≤ q.1+r-1
          · apply sup_eq_right.mpr at h2
            rw [h2]
            ring_nf
          · apply lt_of_not_ge at h2
            apply le_of_lt at h2
            have h3 : q.1+r-1 ≤ 0 := by exact h2
            apply sup_eq_left.mpr at h2
            rw [h2]
            have hp : p.1-1 ≤ 0 := sub_nonpos.mpr p.2.2
            apply sup_eq_left.mpr at hp
            rw [add_zero, hp]
            simp only [sup_eq_left, tsub_le_iff_right, zero_add, ge_iff_le]
            calc p.1+q-1+r
                _ = p+(q+r-1) := by ring
                _ ≤ p+0 := by apply add_le_add_left; exact h3
                _ ≤ 1 := by rw [add_zero]; exact le_one p
        · apply lt_of_not_ge at h
          apply le_of_lt at h
          have h2 : p.1+q-1 ≤ 0 := by exact h
          apply sup_eq_left.mpr at h
          rw [h, zero_add]
          have hr : r.1-1 ≤ 0 := sub_nonpos.mpr r.2.2
          apply sup_eq_left.mpr at hr
          rw [hr]

          by_cases h3 : q.1+r-1 ≤ 0
          · apply sup_eq_left.mpr at h3
            rw [h3]
            simp only [add_zero, left_eq_sup, tsub_le_iff_right, zero_add, ge_iff_le]
            exact le_one p
          · apply lt_of_not_ge at h3
            apply le_of_lt at h3
            have h4 : 0 ≤ q.1+r-1 := by exact h3
            apply sup_eq_right.mpr at h3
            rw [h3]
            simp only [left_eq_sup, tsub_le_iff_right, zero_add, ge_iff_le]
            calc p.1+(q+r-1)
                _ = (p+q-1)+r := by ring
                _ ≤ 0+r := by apply add_le_add_right; exact h2
                _ ≤ 1 := by rw [zero_add]; exact le_one r
    mul_comm p q := by simp only [Subtype.mk.injEq]; rw [add_comm]
    mul_one p := by
        simp only [Set.Icc.coe_one, add_sub_cancel_right]
        have h : 0 ⊔ p = p := by simp only [zero_le', sup_of_le_right]
        exact_mod_cast h
    mul_le_mul_left p q := by
        intro h r
        simp only [Subtype.mk_le_mk, le_sup_iff, sup_le_iff, le_refl, tsub_le_iff_right, zero_add,
          true_and, sub_nonneg, sub_add_cancel, add_le_add_iff_left, Subtype.coe_le_coe]
        by_cases h2 : r.1+p ≤ 1

        left; exact h2

        right; constructor
        apply lt_of_not_ge at h2
        apply le_of_lt at h2
        calc 1
            _ ≤ r.1+p := by exact h2
            _ ≤ r+q := by apply add_le_add_left; exact h
        exact h

theorem luk_cont : LukTnorm'.Continuous := by
  apply (cont_def LukTnorm').mpr
  have hasf : (Function.uncurry LukTnorm'.mul) = (fun p : I×I => ⟨max 0 (p.1.1+p.2-1), luk_max_mem_I p.1 p.2⟩) := by rfl
  rw [hasf]
  refine Continuous.subtype_mk ?_ ?_
  apply Continuous.max
  exact continuous_const
  refine Continuous.add ?_ ?_
  apply Continuous.add (Continuous.fst' continuous_subtype_val) (Continuous.snd' continuous_subtype_val)
  exact continuous_const
def LukTnorm : ContinuousTnorm := LukTnorm'.toContinuousTnorm luk_cont
theorem luk_tnorm_def (p q : I) : LukTnorm.mul p q = 0 ⊔ (p.1+q-1) := by rfl



noncomputable def ProdFuzzy : FuzzyLogic ProdTnorm.toTnorm where
  and_def p q := by rfl
  imp_def p q := by rfl
noncomputable def MinFuzzy : FuzzyLogic MinTnorm.toTnorm where
  and_def p q := by rfl
  imp_def p q := by rfl
noncomputable def LukFuzzy : FuzzyLogic LukTnorm.toTnorm where
  and_def p q := by rfl
  imp_def p q := by rfl



noncomputable
def DrasticTnorm : Tnorm where
    mul p q := if p = 1 ∨ q = 1 then min p q else 0
    mul_assoc p q r := by
      by_cases hp : p = 1
      by_cases hq : q = 1
      simp only [hp, hq, or_self, ↓reduceIte, min_self, true_or, inf_eq_left, inf_le_left,
        inf_of_le_right]

      by_cases hr : r = 1
      simp only [hp, hq, or_false, ↓reduceIte, min_comm, inf_eq_right, hr, or_true, inf_le_right,
        inf_of_le_left, true_or, inf_of_le_right]

      have hq2 : ¬1 ≤ q := by apply not_le_of_lt; apply unitInterval.lt_one_iff_ne_one.mpr hq
      simp only [hp, hq, or_false, ↓reduceIte, inf_eq_left, hq2, hr, or_self, zero_ne_one, zero_le',
        inf_of_le_right]

      by_cases hq : q = 1
      by_cases hr : r = 1
      simp only [hp, hq, or_true, ↓reduceIte, inf_eq_right, hr, inf_le_right, inf_of_le_left,
        or_self, min_self]

      have hp2 : ¬1 ≤ p := by apply not_le_of_lt; apply unitInterval.lt_one_iff_ne_one.mpr hp
      have hr2 : ¬1 ≤ r := by apply not_le_of_lt; apply unitInterval.lt_one_iff_ne_one.mpr hr
      simp only [hp, hq, or_true, ↓reduceIte, inf_eq_right, hp2, hr, or_self, or_false, inf_eq_left,
        hr2]

      by_cases hr : r = 1
      have hq2 : ¬1 ≤ q := by apply not_le_of_lt; apply unitInterval.lt_one_iff_ne_one.mpr hq
      simp only [hp, hq, or_self, ↓reduceIte, zero_ne_one, hr, or_true, zero_le', inf_of_le_left,
        inf_eq_right, hq2]

      simp only [hp, hq, or_self, ↓reduceIte, zero_ne_one, hr]
    mul_comm p q := by
        by_cases h : p = 1 ∨ q = 1
        have h2 : q = 1 ∨ p = 1 := by apply Or.symm h
        simp only [h, ↓reduceIte, h2]
        exact min_comm p q

        have h2 : ¬(q = 1 ∨ p = 1) := by exact fun a ↦ h (id (Or.symm a))
        simp only [h, ↓reduceIte, h2]
    mul_one p := by
        simp only [or_true, ↓reduceIte, inf_eq_left]
        exact le_one p
    mul_le_mul_left p q h r := by
      by_cases hr : r = 1
      simp only [hr, true_or, ↓reduceIte, le_inf_iff, inf_le_left, inf_le_iff, true_and]
      right; exact h

      by_cases hq : q = 1
      simp only [hr, false_or, hq, or_true, ↓reduceIte, le_inf_iff]
      constructor
      by_cases hp : p = 1
      simp only [hp, ↓reduceIte, inf_le_left]
      simp only [hp, ↓reduceIte, zero_le']

      by_cases hp : p = 1
      simp only [hp, ↓reduceIte, inf_le_right]
      simp only [hp, ↓reduceIte, zero_le']

      have hp : ¬p=1 := by apply unitInterval.lt_one_iff_ne_one.mp; calc p
        _ ≤ q := h
        _ < 1 := unitInterval.lt_one_iff_ne_one.mpr hq
      simp only [hr, hp, or_self, ↓reduceIte, hq, le_refl]
lemma drastic_def (p q : I) : DrasticTnorm.mul p q = (if p = 1 ∨ q = 1 then min p q else 0) := by rfl

lemma luk_imp_min_I (p q : I) : 1 ⊓ (1-p.1+q) ∈ I := by
  constructor
  apply le_min zero_le_one
  calc 0
    _ ≤ 1-p.1 := one_minus_nonneg p
    _ ≤ 1-p.1+q := by apply le_add_of_le_of_nonneg ?_ q.2.1; rfl;
  apply min_le_left

lemma luk_imp_min (p q : I) : Tnorm.LukFuzzy.imp p q = ⟨min 1 (1 - p.1 + q), luk_imp_min_I p q⟩ := by
  let r : I := ⟨min 1 (1 - p.1 + q), luk_imp_min_I p q⟩
  have himple : r ≤ Tnorm.LukFuzzy.imp p q := by
    apply (FuzzyLogic.le_imp_iff_and_le Tnorm.LukFuzzy p q r).mp
    apply Subtype.coe_le_coe.mp
    rw [← max_eq_right q.2.1]
    apply max_le_max_left
    calc r.1+p-1
    _ = p + min 1 (1-p.1+q)-1 := by ring
    _ ≤ p+(1-p.1+q)-1 := by refine tsub_le_tsub_right ?_ 1; refine add_le_add ?_ ?_; rfl; exact min_le_right (1 : ℝ) (1-p+q)
    _ = q := by ring

  apply antisymm ?_ himple
  rw [Tnorm.LukFuzzy.imp_def]

  apply sSup_le
  intro a ha; rw [Set.mem_setOf] at ha
  unfold r; apply Subtype.mk_le_mk.mpr
  apply le_inf a.2.2
  have hamul : LukTnorm.mul p a = 0 ⊔ (p.1+a-1) := by rfl
  apply Subtype.coe_le_coe.mpr at ha; rw [hamul] at ha; apply le_of_max_le_right at ha
  calc a.1
    _ = (1-p)+(p+a-1) := by ring
    _ ≤ (1-p)+q := by apply add_le_add_left ha
