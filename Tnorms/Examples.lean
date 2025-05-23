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
  * the nilpotent minimum T-norm
  * the drastic T-norm
-/
namespace Tnorm

def ProdTnorm' : Tnorm where
  mul p q := ⟨p*q, unitInterval.mul_mem p.2 q.2⟩
  mul_assoc p q r := by
    simp
    apply_mod_cast Real.commRing.mul_assoc
  mul_comm p q := by
    simp
    apply_mod_cast Real.commRing.mul_comm
  mul_one p := by simp
  mul_le_mul_left p q := by
    intro h
    intro r
    simp
    apply_mod_cast Real.orderedSemiring.mul_le_mul_of_nonneg_left p q r
    exact h
    exact nonneg r
/-theorem prod_cont : ProdTnorm'.Continuous := by
  apply (cont_def ProdTnorm').mpr
  sorry
def ProdTnorm : ContinuousTnorm := ProdTnorm'.toContinuousTnorm prod_cont-/
def ProdTnorm := ProdTnorm'

def MinTnorm' : Tnorm where
    mul p q := min p q
    mul_assoc p q r := by
        simp
        exact min_assoc p q r
    mul_comm p q := by
        simp
        exact min_comm p q
    mul_one p := by
        simp
        exact le_one p
    mul_le_mul_left p q := by
        intro h
        intro r
        simp
        right
        exact h
theorem min_cont : MinTnorm'.Continuous := (cont_def MinTnorm').mpr continuous_min
def MinTnorm : ContinuousTnorm := MinTnorm'.toContinuousTnorm min_cont


def LukTnorm' : Tnorm where
    mul p q := ⟨max 0 (p+q-1), by
        simp
        calc p.1 + q
            _ = p+q := by rfl
            _ ≤ p+1 := by apply add_le_add_left; exact_mod_cast le_one q
            _ ≤ 1+1 := by apply add_le_add_right; exact_mod_cast le_one p
        ⟩
    mul_assoc p q r := by
        simp
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
            have hp : p.1-1 ≤ 0 := by
                refine sub_nonpos.mpr ?_
                exact le_one p
            apply sup_eq_left.mpr at hp
            simp
            rw [hp]
            simp
            calc p.1+q-1+r
                _ = p+(q+r-1) := by ring
                _ ≤ p+0 := by apply add_le_add_left; exact h3
                _ ≤ 1 := by simp; exact le_one p
        · apply lt_of_not_ge at h
          apply le_of_lt at h
          have h2 : p.1+q-1 ≤ 0 := by exact h
          apply sup_eq_left.mpr at h
          rw [h]
          simp
          have hr : r.1-1 ≤ 0 := by
            refine sub_nonpos.mpr ?_
            exact le_one r
          apply sup_eq_left.mpr at hr
          rw [hr]

          by_cases h3 : q.1+r-1 ≤ 0
          · apply sup_eq_left.mpr at h3
            rw [h3]
            simp
            exact le_one p
          · apply lt_of_not_ge at h3
            apply le_of_lt at h3
            have h4 : 0 ≤ q.1+r-1 := by exact h3
            apply sup_eq_right.mpr at h3
            rw [h3]
            simp
            calc p.1+(q+r-1)
                _ = (p+q-1)+r := by ring
                _ ≤ 0+r := by apply add_le_add_right; exact h2
                _ ≤ 1 := by simp; exact le_one r
    mul_comm p q := by
        simp
        rw [add_comm]
    mul_one p := by
        simp
        have h : 0 ⊔ p = p := by simp
        exact_mod_cast h
    mul_le_mul_left p q := by
        intro h
        intro r
        simp

        by_cases h2 : r.1+p ≤ 1

        left
        exact h2

        right
        constructor
        apply lt_of_not_ge at h2
        apply le_of_lt at h2
        calc 1
            _ ≤ r.1+p := by exact h2
            _ ≤ r+q := by apply add_le_add_left; exact h
        exact h

theorem luk_cont : LukTnorm'.Continuous := by
  sorry
def LukTnorm : ContinuousTnorm := LukTnorm'.toContinuousTnorm luk_cont


/-left_cont_x p q := by
intro ε he
use ε
constructor
exact he
intro r hrl hrg
simp
apply abs_sub_lt_iff.mpr
constructor

by_cases hr : r.1+q-1 ≤ 0
simp [hr]
apply neg_lt_of_neg_lt
calc -ε
  _ < 0 := by simp; exact he
  _ ≤ 0 ⊔ (p.1+q-1) := by exact le_max_left 0 (p.1+q-1)

apply lt_of_not_ge at hr
apply le_of_lt at hr
simp [hr]
calc (r.1+q-1)-(0 ⊔ (p.1+q-1))
  _ ≤ (r.1+q-1)-(p.1+q-1) := by refine sub_le_sub ?_ ?_; rfl; exact le_max_right 0 (p.1+q-1)
  _ = r.1-p := by ring
  _ ≤ 0 := by exact tsub_nonpos.mpr hrg;
  _ < ε := by exact he

by_cases hp : p.1+q-1 ≤ 0
simp [hp]
apply neg_lt_of_neg_lt
calc -ε
  _ < 0 := by simp; exact he
  _ ≤ 0 ⊔ (r.1+q-1) := by apply le_max_left 0 (r.1+q-1);

apply lt_of_not_ge at hp
apply le_of_lt at hp
simp [hp]
calc (p.1+q-1)-(0 ⊔ (r.1+q-1))
  _ ≤ (p.1+q-1)-(r.1+q-1) := by refine sub_le_sub ?_ ?_; rfl; exact le_max_right 0 (r.1+q-1)
  _ = p.1-r := by ring
  _ < ε := by exact sub_lt_comm.mp hrl-/




noncomputable def ProdFuzzy : FuzzyLogic ProdTnorm where
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
    mul p q := if p = 1 ∨ q = 1 then min p q
                else 0
    mul_assoc p q r := by
      by_cases hp : p = 1
      by_cases hq : q = 1
      simp [hp, hq]

      by_cases hr : r = 1
      simp [hp, hq, hr, min_comm]

      have hq2 : ¬1 ≤ q := by apply not_le_of_lt; apply unitInterval.lt_one_iff_ne_one.mpr hq
      simp [hp, hq, hq2, hr]

      by_cases hq : q = 1
      by_cases hr : r = 1
      simp [hp, hq, hr]

      have hp2 : ¬1 ≤ p := by apply not_le_of_lt; apply unitInterval.lt_one_iff_ne_one.mpr hp
      have hr2 : ¬1 ≤ r := by apply not_le_of_lt; apply unitInterval.lt_one_iff_ne_one.mpr hr
      simp [hp, hq, hr, hp2, hr2]

      by_cases hr : r = 1
      have hq2 : ¬1 ≤ q := by apply not_le_of_lt; apply unitInterval.lt_one_iff_ne_one.mpr hq
      simp [hp, hq, hr, hq2]

      simp [hp, hq, hr]
    mul_comm p q := by
        by_cases h : p = 1 ∨ q = 1
        have h2 : q = 1 ∨ p = 1 := by exact id (Or.symm h)
        simp [h, h2]
        exact min_comm p q

        have h2 : ¬(q = 1 ∨ p = 1) := by exact fun a ↦ h (id (Or.symm a))
        simp [h, h2]
    mul_one p := by
        simp
        exact le_one p
    mul_le_mul_left p q h r := by
      by_cases hr : r = 1
      simp [hr]
      right
      exact h

      by_cases hq : q = 1
      simp [hr, hq]
      constructor
      by_cases hp : p = 1
      simp [hp]
      simp [hp]

      by_cases hp : p = 1
      simp [hp]
      simp [hp]

      have hq2 : q < 1 := by apply unitInterval.lt_one_iff_ne_one.mpr hq
      have hp : ¬p=1 := by apply unitInterval.lt_one_iff_ne_one.mp; calc p
        _ ≤ q := by exact h
        _ < 1 := by exact hq2
      simp [hr, hq, hp]



lemma luk_imp_min (p q : I) : Tnorm.LukFuzzy.imp p q = min 1 (1 - p.1 + q) := by
  rw [Tnorm.LukFuzzy.imp_def]
  refine csSup_eq_of_is_forall_le_of_forall_le_imp_ge ?_ ?_ ?_

  use 0
  simp

  simp
  intro a
  intro ha
  intro hmul

  constructor
  exact ha.right

  refine tsub_le_iff_left.mp ?_
  calc a - (1 - p)
    _ = p+a-1 := by ring
    _ ≤ q := by exact le_of_max_le_right hmul

  intro ub
  intro h
  specialize h (min 1 (1-p+q))
  apply h
  simp

  have hpq : 0 ≤ 1-p.1+q := by
    calc 0
    _ ≤ 1-p.1 := by exact one_minus_nonneg p
    _ = 1-p.1+0 := by simp
    _ ≤ 1-p.1+q := by apply add_le_add; rfl; exact nonneg q
  use hpq
  have pqI : min 1 (1-p.1+q) ∈ I := by
    simp
    exact hpq

  have h2 : p + (min 1 (1-p.1+q)) - 1 ≤ q := by
    calc p + min 1 (1-p.1+q)-1
    _ ≤ p+(1-p.1+q)-1 := by refine tsub_le_tsub_right ?_ 1; refine add_le_add ?_ ?_; rfl; exact min_le_right (1 : ℝ) (1-p+q)
    _ = q := by ring

  have h3 : max 0 (p + (min 1 (1-p.1+q)) - 1) ≤ q := by
    calc max 0 (p + (min 1 (1-p.1+q)) - 1)
      _ ≤ max 0 q.1 := by exact max_le_max_left 0 h2
      _ = q := by refine max_eq_right ?_; exact nonneg q

  have h4 : Tnorm.LukTnorm.mul p ⟨min 1 (1-p.1+q), pqI⟩ ≤ max 0 q := by exact max_le_max_left 0 h2

  calc Tnorm.LukTnorm.mul p ⟨min 1 (1-p.1+q), pqI⟩
  _ ≤ max 0 q := by exact h4
  _ = q := by refine max_eq_right (nonneg q)
