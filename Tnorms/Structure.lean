import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Examples
import Tnorms.Algebra
import Tnorms.LeftContinuity
import Tnorms.Continuity
import Tnorms.LeftContinuousArchimedean
import Tnorms.RatPow
import Tnorms.RealPow

import Mathlib.Tactic.Rify
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Basic


open unitInterval

lemma zero_sq_of_nilpt_el {T : Tnorm} : HasNilpotent T → ∃ p : I, T.npow 2 p = 0 ∧ IsNontrivial p := by
  intro h
  obtain ⟨q, hqnt, n, hpow⟩ := h
  let m := sSup {n : ℕ | T.npow n q > 0}
  have hbdd : BddAbove ({n | T.npow n q > 0}) := by
    apply bddAbove_def.mpr
    use n; intro y; contrapose!; intro hny
    apply le_of_lt at hny
    apply T.npow_le_self n y q at hny; rw[hpow] at hny
    apply Set.notMem_setOf_iff.mpr (not_lt_of_le hny)
  have hm : 1 ≤ m := by
      apply le_csSup hbdd
      apply Set.mem_setOf.mpr; rw [T.npow_one]
      exact unitInterval.pos_iff_ne_zero.mpr hqnt.1
  use T.npow m q; constructor; swap; constructor
  apply unitInterval.pos_iff_ne_zero.mp
  have hm : m ∈ {n | T.npow n q > 0} := by
    apply Nat.sSup_mem ?_ hbdd
    use 0; apply Set.mem_setOf_eq.mpr; rw [T.npow_zero]; exact zero_lt_one
  apply Set.mem_setOf_eq.mp hm

  apply unitInterval.lt_one_iff_ne_one.mp
  calc T.npow m q
    _ ≤ T.npow 1 q := T.npow_le_self 1 m q hm
    _ = q := T.npow_one q
    _ < 1 := unitInterval.lt_one_iff_ne_one.mpr hqnt.2

  apply le_zero_iff.mp
  calc T.npow 2 (T.npow m q)
    _ = T.npow (2*m) q := T.npow_mul m 2 q
    _ ≤ T.npow (m+1) q := T.npow_le_self (m+1) (2*m) q (add_one_le_two_mul hm)
    _ = 0 := by
      apply le_zero_iff.mp
      suffices m+1 ∉ {n | T.npow n q > 0} by exact le_of_not_lt this
      apply notMem_of_csSup_lt (lt_add_one m) hbdd

lemma zero_sq_nonempty {T : Tnorm} : Nilpotent T → {p : I | T.npow 2 p = 0}.Nonempty := by
  intro h
  apply nilpt_el_of_nilpt at h
  apply zero_sq_of_nilpt_el at h
  obtain ⟨p, hp, hpnt⟩ := h
  use p; exact hp


theorem luk_iso_of_nilpt {T : Tnorm} : Nilpotent T → Tnorm.Isomorphic Tnorm.LukTnorm.toTnorm T := by
  intro h
  let L := Tnorm.LukTnorm
  let T :=  T.toContinuousTnorm h.1
  let a : I := sSup {p : I | T.npow 2 p = 0}
  have ha2 : T.pow 2 a = 0 := by
    have hpr : T.pow 2 a = T.rpow 2 a := by exact_mod_cast T.pow_cast 2 a
    have hrn : T.rpow 2 a = T.npow 2 a := by exact_mod_cast T.rpow_cast 2 a
    rw [hpr, hrn]
    suffices IsClosed {p : I | T.npow 2 p = 0} by
      apply IsClosed.sSup_mem at this
      specialize this
      rw [Set.mem_setOf] at this; unfold a
      exact this
      exact zero_sq_nonempty h
    exact isClosed_eq (Tnorm.npow_cont T 2) continuous_const
  have ha0 : ∀ t : ℝ, t ≥ 2 → T.pow t a = 0 := by
    intro t ht
    apply T.pow_anti a at ht
    unfold ContinuousTnorm.powp at ht
    rw [ha2] at ht
    apply antisymm ht
    exact (T.pow t a).2.1
  have ha1 : ∀ t : ℝ, t ≤ 0 → T.pow t a = 1 := by
    intro t ht
    rw [T.pow_nonpos]; exact ht
  have hant : IsNontrivial a := by
    constructor
    apply unitInterval.pos_iff_ne_zero.mp
    obtain ⟨p, hp, hpnt⟩ := zero_sq_of_nilpt_el (nilpt_el_of_nilpt T.toTnorm h)
    apply And.left at hpnt; apply unitInterval.pos_iff_ne_zero.mpr at hpnt
    apply lt_of_lt_of_le hpnt
    apply le_sSup;
    exact Set.mem_setOf.mp hp

    apply_fun (T.npow 2)
    rw [T.npow_I_one]
    specialize ha0 2 ?_; rfl
    rw_mod_cast [← Tnorm.rpow_cast, ← T.pow_cast, ha0]
    exact zero_ne_one' ↑I
  have has : sSup {t | T.pow t a ≠ 0} = 2 := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (T.nonzeropow_nonempty a)
    intro t ht; rw [Set.mem_setOf] at ht
    specialize ha0 t
    contrapose! ht
    specialize ha0 (le_of_lt ht)
    exact ha0

    intro w hw;
    obtain ⟨r, hrw, hr⟩ := exists_rat_btwn hw
    use r; constructor; swap; exact hrw
    rw [Set.mem_setOf, T.pow_cast]
    by_cases hr0 : r ≤ 0
    rw [Tnorm.zero_rpow r a hr0]
    exact one_ne_zero

    let b := T.rpow (r/2) a
    suffices b > a by
      suffices b ∉ {p | T.npow 2 p = 0} by
        rw [Set.mem_setOf] at this
        unfold b at this; push_neg at this; push_neg at hr0
        rw [T.npow_two,
          ← Tnorm.rpow_add (r/2) (r/2) a (le_of_lt (half_pos hr0)) (le_of_lt (half_pos hr0)),
          add_halves] at this
        exact this
      contrapose! this
      apply le_sSup this
    rw [← T.npow_one a, ← T.rpow_cast]; unfold b
    apply Tnorm.rpow_strict_anti (arch_of_nilpt T.toTnorm h)
    refine (div_lt_iff₀' rfl).mpr ?_; rw [Nat.cast_one, mul_one]; exact_mod_cast hr
    exact hant; push_neg at hr0; exact le_of_lt (half_pos hr0)
    apply le_csSup; swap;
    simp only [ne_eq, Nat.cast_one, Rat.cast_one, Set.mem_image, Set.mem_setOf_eq]
    use 1; simp only [Rat.cast_one, and_true]; push_neg
    have hrnpow : T.rpow 1 a = T.npow 1 a := by rw [← Tnorm.rpow_cast 1 a]; rfl
    rw [hrnpow, T.npow_one]; exact hant.1

    apply bddAbove_def.mpr
    apply And.right at h
    specialize h a hant; obtain ⟨n, hn⟩ := h
    use n; intro y hy; simp only [ne_eq, Set.mem_image, Set.mem_setOf_eq] at hy
    obtain ⟨y', hy, hyy'⟩ := hy
    apply unitInterval.pos_iff_ne_zero.mpr at hy
    contrapose! hy
    rw [← hn, ← Tnorm.rpow_cast n a]
    apply Tnorm.rpow_le_self; rw [← hyy'] at hy; exact_mod_cast le_of_lt hy


  let f : Set.Icc (0:ℝ) 2 → I := fun x => T.pow x a
  have hfb : Function.Bijective f := by
    constructor
    let hi := T.pow_inj h a hant
    rw [has] at hi
    intro p q hpq; apply Subtype.coe_inj.mp
    exact hi p.2 q.2 hpq

    let hs := T.pow_surj h a hant
    intro p
    specialize hs p; obtain ⟨b, hs⟩ := hs
    by_cases h0 : b ≤ 0
    apply ha1 b at h0; unfold ContinuousTnorm.powp at hs; rw [h0] at hs
    use ⟨0, by constructor; rfl; exact zero_le_two⟩
    rw [← hs]; unfold f; apply ha1; rfl

    by_cases h2 : b ≥ 2
    apply ha0 b at h2; unfold ContinuousTnorm.powp at hs; rw [h2] at hs
    use ⟨2, by constructor; exact zero_le_two; rfl⟩
    rw [← hs]; unfold f; apply ha0; rfl

    push_neg at h0; push_neg at h2
    use ⟨b, by constructor; exact le_of_lt h0; exact le_of_lt h2⟩
    exact hs
  have hfa : Antitone f := by intro p q hpq; exact T.pow_anti a hpq
  have hfx' : ∀ r s : Set.Icc (0 : ℝ) 2, T.mul (f r) (f s) = T.pow (r+s) a := by
    intro r s; symm
    apply T.pow_add h; exact hant; exact r.2.1; exact s.2.1
  have hfx : ∀ r s t : Set.Icc (0 : ℝ) 2, r.1+s=t → (f t) = T.mul (f r) (f s) := by
    intro r s t hrst; specialize hfx' r s; rw [hfx', hrst]


  let g : I → Set.Icc (0 : ℝ) 2 := fun p => ⟨2*p, by
    constructor; exact mul_nonneg (zero_le_two) p.2.1
    nth_rw 2 [← MulOneClass.mul_one 2]
    exact (mul_le_mul_iff_of_pos_left zero_lt_two).mpr p.2.2
    ⟩
  have hgb : Function.Bijective g := by
    constructor
    intro p q hpq; unfold g at hpq;
    simp only [Subtype.mk.injEq, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at hpq
    exact SetCoe.ext hpq

    intro a; use ⟨a/2, by
      constructor
      exact div_nonneg a.2.1 zero_le_two
      exact (div_le_one₀ zero_lt_two).mpr a.2.2
      ⟩
    unfold g; field_simp
  have hgm : Monotone g := by
    intro p q hpq; unfold g; apply Subtype.mk_le_mk.mpr
    apply Subtype.coe_le_coe.mpr at hpq
    apply (mul_le_mul_left zero_lt_two).mpr hpq

  have hsb : Function.Bijective σ := by
    apply Function.bijective_iff_has_inverse.mpr
    use σ; constructor;
    exact symm_symm; exact symm_symm
  have hsa : Antitone σ := by intro p q hpq; exact symm_le_symm.mpr hpq

  let φ := f ∘ g ∘ σ

  use φ; constructor; constructor
  exact Function.Bijective.comp hfb (Function.Bijective.comp hgb hsb)
  exact Antitone.comp hfa (Monotone.comp_antitone hgm hsa)


  intro p q
  unfold φ
  have ht : Tnorm.LukTnorm.mul p q = 0 ⊔ (p.1+q-1) := by rfl
  simp only [Function.comp_apply]
  by_cases hpq : p.1+q-1 ≥ 0
  apply hfx (g (σ p)) (g (σ q)) (g (σ (L.mul p q)))
  unfold g; simp only [coe_symm_eq]
  calc 2*(1-p.1) + 2*(1-q)
    _ = 2*(1-(p.1+q-1)) := by ring
    _ = 2*(1-(L.mul p q)) := by congr; rw [ht]; exact Eq.symm (max_eq_right hpq)

  specialize hfx' (g (σ p)) (g (σ q)); push_neg at hpq
  have hf0 : f (g (σ (Tnorm.LukTnorm.mul p q))) = 0 := by
    suffices (Tnorm.LukTnorm.mul p q) = 0 by
      rw [this, symm_zero]; unfold g
      simp only [Set.Icc.coe_one, mul_one]
      unfold f; apply ha0 2 ?_; rfl
    rw [max_eq_left (le_of_lt hpq)] at ht
    exact SetCoe.ext ht
  have hgs : (g (σ p)).1+(g (σ q)) ≥ 2 := by
    unfold g; simp only [coe_symm_eq]
    apply le_of_lt
    calc 2*(1-p.1)+2*(1-q)
      _ = 2*(1-(p.1+q-1)) := by ring
      _ > 2*(1-0) := by
        apply (mul_lt_mul_left zero_lt_two).mpr
        rw [sub_zero]
        apply lt_tsub_comm.mp
        rw [sub_self]
        exact hpq
      _ = 2 := by ring
  specialize ha0 ((g (σ p)).1+(g (σ q))) hgs
  rw [ha0] at hfx'; rw [hf0, ← hfx']; rfl
