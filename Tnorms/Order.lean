import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Examples


import Mathlib.Topology.UnitInterval

open unitInterval


-- Define a partial order on t-norms

section namespace Tnorm


instance le : LE Tnorm :=
  ⟨fun T₁ T₂ => ∀ p q : I, T₁.mul p q ≤ T₂.mul p q⟩

instance : PartialOrder Tnorm :=
  { Tnorm.le with
  le_refl := by intro T p q; rfl
  le_trans := by
    intro T₁ T₂ T₃ h12 h23 p q
    specialize h12 p q; specialize h23 p q
    exact le_trans h12 h23
  le_antisymm := by
    intro T₁ T₂ h12 h21
    ext p q
    specialize h12 p q; specialize h21 p q
    apply Subtype.coe_inj.mpr
    exact antisymm h12 h21
  }
instance : Preorder Tnorm := inferInstance

instance : OrderTop Tnorm :=
  { Tnorm.le with
  top := Tnorm.MinTnorm.toTnorm
  le_top := by
    intro T p q
    have hmin : MinTnorm.mul p q = p ⊓ q := by rfl
    rw [hmin]
    apply le_min
    exact mul_le_left p q
    exact mul_le_right p q
  }
noncomputable
instance : OrderBot Tnorm :=
  { Tnorm.le with
  bot := Tnorm.DrasticTnorm
  bot_le := by
    intro T p q
    by_cases hpq : p = 1 ∨ q = 1
    unfold DrasticTnorm
    simp only [hpq, ↓reduceIte, inf_le_iff]

    by_cases hp : p = 1
    right; rw [hp, T.one_mul]
    simp only [hp, false_or] at hpq
    left; rw [hpq, T.mul_one]

    unfold DrasticTnorm
    simp only [hpq, ↓reduceIte, zero_le']
  }
theorem min_top : ⊤ = Tnorm.MinTnorm.toTnorm := by rfl
theorem min_top' : ⊤ = Tnorm.MinTnorm' := by rfl
theorem drastic_bot : ⊥ = Tnorm.DrasticTnorm := by rfl



end Tnorm

lemma half_mem_I : 1/2 ∈ I := by apply unitInterval.div_mem zero_le_one zero_le_two one_le_two

theorem luk_lt_prod : Tnorm.LukTnorm.toTnorm < Tnorm.ProdTnorm.toTnorm := by
  apply lt_of_le_of_ne
  intro p q; apply Subtype.coe_le_coe.mp
  rw [Tnorm.luk_tnorm_def, Tnorm.prod_tnorm_def]
  apply max_le; unit_interval
  suffices p.1*q-p-q+1 ≥ 0 by
    push_cast
    apply sub_nonneg.mp ?_
    ring_nf; ring_nf at this
    exact this
  calc p.1*q-p-q+1
    _ = (p.1-1)*(q-1) := by ring
    _ ≥ 0 := by
      refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
      simp only [tsub_le_iff_right, zero_add]; exact p.2.2
      simp only [tsub_le_iff_right, zero_add]; exact q.2.2

  by_contra h
  let p : I := ⟨1/2, half_mem_I⟩
  have hlp : Tnorm.LukTnorm.mul p p = Tnorm.ProdTnorm.mul p p := by rw [h]
  apply Subtype.coe_inj.mpr at hlp
  rw [Tnorm.luk_tnorm_def, Tnorm.prod_tnorm_def] at hlp
  unfold p at hlp; simp only [Set.Icc.coe_mul] at hlp
  ring_nf at hlp
  simp only [max_self, one_div, zero_eq_inv, OfNat.zero_ne_ofNat] at hlp

theorem drastic_lt_luk : Tnorm.DrasticTnorm < Tnorm.LukTnorm.toTnorm := by
  refine IsBot.lt_of_ne ?_ ?_
  exact isBot_iff_eq_bot.mpr rfl
  by_contra h
  let p : I := ⟨3/4, by
    apply unitInterval.div_mem zero_le_three zero_le_four ?_
    have htf : (3 : ℕ) ≤ (4 : ℕ) := by decide
    exact_mod_cast htf
  ⟩
  have hp1 : p ≠ 1 := by
    apply unitInterval.lt_one_iff_ne_one.mp
    unfold p;
    refine coe_lt_one.mp ?_
    simp only
    refine (div_lt_one zero_lt_four).mpr ?_
    have htf : (3 : ℕ) < (4 : ℕ) := by decide
    exact_mod_cast htf
  have hdl : Tnorm.DrasticTnorm.mul p p = Tnorm.LukTnorm.mul p p := by rw [h]
  have hdp : Tnorm.DrasticTnorm.mul p p = 0 := by
    unfold Tnorm.DrasticTnorm;
    simp only [hp1, or_self, ↓reduceIte]
  have hlp : Tnorm.LukTnorm.mul p p = ⟨1/2, half_mem_I⟩ := by
    apply Subtype.coe_inj.mp
    rw [Tnorm.luk_tnorm_def, Subtype.coe_mk]; simp only
    ring_nf
    refine max_eq_right half_mem_I.1

  rw [hdp, hlp] at hdl
  have hzh : 0 ≠ (1:ℝ)/2 := by simp only [one_div, ne_eq, zero_eq_inv, OfNat.zero_ne_ofNat, not_false_eq_true]
  apply Subtype.coe_inj.mpr at hdl
  exact hzh hdl

theorem prod_lt_min : Tnorm.ProdTnorm.toTnorm < Tnorm.MinTnorm.toTnorm := by
  apply IsTop.lt_of_ne (isTop_iff_eq_top.mpr rfl)
  by_contra h
  let p : I := ⟨1/2, half_mem_I⟩
  have hpm : Tnorm.ProdTnorm.mul p p = Tnorm.MinTnorm.mul p p := by rw [h]; rfl
  rw [Tnorm.prod_tnorm_def, Tnorm.min_tnorm_def, min_self] at hpm
  unfold p at hpm
  apply Subtype.mk_eq_mk.mp at hpm
  simp only [one_div, ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀,
    inv_eq_one, OfNat.ofNat_ne_one] at hpm
