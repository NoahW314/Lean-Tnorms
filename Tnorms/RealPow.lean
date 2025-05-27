import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Examples
import Tnorms.Algebra
import Tnorms.LeftContinuity
import Tnorms.Continuity
import Tnorms.LeftContinuousArchimedean
import Tnorms.RatPow
import Tnorms.SupInfI

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Instances.Real.Lemmas


open unitInterval

section namespace ContinuousTnorm

variable {T : ContinuousTnorm}

noncomputable
def pow (t : ℝ) (p : I) : I := sInf ((fun s : ℚ => T.rpow s p) '' {s : ℚ | s ≤ t})
noncomputable
def powp (p : I) : ℝ → I := fun r => T.pow r p

theorem pow_cast (r : ℚ) (p : I) : T.pow r p = T.rpow r p := by
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  intro a ha; simp only [Rat.cast_le, Set.mem_image, Set.mem_setOf_eq] at ha
  obtain ⟨x, hxr, hxp⟩ := ha
  rw [← hxp]; apply Tnorm.rpow_le_self T r x p hxr

  intro w hw
  use (T.toTnorm.rpow r p); simp only [Rat.cast_le, Set.mem_image, Set.mem_setOf_eq]
  constructor; use r; exact hw

@[simp] lemma pow_zero (p : I) : T.pow 0 p = 1 := by
  have h : T.pow 0 p = T.rpow 0 p := by exact_mod_cast pow_cast 0 p
  have h2 : T.rpow 0 p = T.npow 0 p := by exact_mod_cast T.rpow_cast 0 p
  rw [h, h2, T.npow_zero]

theorem pow_anti (p : I) : Antitone (T.powp p) := by
  intro r s hrs; unfold powp; unfold pow
  apply sInf_le_sInf
  simp only [Set.image_subset_iff]
  intro t ht; simp only [Set.mem_setOf_eq] at ht
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
  use t; constructor; exact le_trans ht hrs; rfl

@[simp] lemma pow_nonpos (t : ℝ) (p : I) (ht : t ≤ 0) : T.pow t p = 1 := by
  let hap := T.pow_anti p ht; unfold powp at hap
  rw [T.pow_zero] at hap
  apply antisymm ?_ hap
  exact (T.pow t p).2.2

lemma ipow_tendsto_one (harch : IsArchimedean T.toTnorm) (a : I) (hant : IsNontrivial a) :
  Filter.Tendsto (fun n : ℕ => T.ipow (n+1) a) Filter.atTop (nhds 1) := by
    have hmt : Monotone (fun n : ℕ => T.ipow (n+1) a) := by
      intro i j hij
      simp only
      apply Tnorm.ipow_le_self T
      exact Ne.symm (Nat.zero_ne_add_one i)
      exact Nat.add_le_add_right hij 1
    let p := ⨆ i, (T.ipow (i+1) a)
    have hlim := tendsto_atTop_iSup hmt
    suffices p ≥ 1 by
      apply antisymm' p.2.2 at this; symm at this
      rw [Set.Icc.coe_eq_one] at this
      rw [← this]; exact hlim
    apply forall_lt_imp_le_iff_le_of_dense.mp
    intro w hw
    unfold p Tnorm.ipow
    suffices ∃ n : ℕ, w ≤ Tnorm.ipow (n+1) a by
      obtain ⟨n, this⟩ := this
      exact le_iSup_of_le n this
    by_cases hw0 : w = 0
    use 0; rw [hw0]; unit_interval
    have hwnt : IsNontrivial w := by
      constructor; exact hw0
      apply unitInterval.lt_one_iff_ne_one.mp hw
    specialize harch w a hwnt hant
    obtain ⟨n, hn⟩ := harch
    use n; apply le_sSup
    rw [Set.mem_setOf]
    apply lt_of_le_of_lt ?_ hn
    apply Tnorm.npow_le_self
    exact Nat.le_add_right n 1

theorem zero_closure_rpow (a : I) (hant : IsNontrivial a) (harch : IsArchimedean T.toTnorm) : 0 ∈ closure (Set.range (fun r => T.rpow r a)) := by
  apply mem_closure_iff_seq_limit.mpr
  apply lp_of_arch at harch
  specialize harch a hant
  use (fun n => T.npow n a); constructor
  intro n; rw [Set.mem_range]
  use n; rw [T.rpow_cast]
  exact harch

theorem one_closure_rpow (a : I) : 1 ∈ closure (Set.range (fun r => T.rpow r a)) := by
  apply subset_closure
  rw [Set.mem_range]
  use 0; rw [Tnorm.zero_rpow]; rfl

theorem rpow_denseInterior (harch : IsArchimedean T.toTnorm) (a : I) (hant : IsNontrivial a) :
  ¬ Dense (Set.range (fun r => T.rpow r a)) → (∃ x ∈ (closure (Set.range (fun r => T.rpow r a)))ᶜ, ∃ p q : I,
  x ∈ Set.Ioo p q ∧ Set.Ioo p q ⊆ (closure (Set.range (fun r => T.rpow r a)))ᶜ) := by
    let D := Set.range (fun r => T.rpow r a)
    intro h
    have hopen : IsOpen (closure D)ᶜ := isOpen_compl_iff.mpr isClosed_closure
    have hnonempty : ((closure D)ᶜ).Nonempty := by
      refine Set.nonempty_compl.mpr ?_
      contrapose! h
      apply dense_iff_closure_eq.mpr h
    obtain ⟨x, hx⟩ := hnonempty
    use x; constructor; unfold D at hx; exact hx
    rw [Set.mem_compl_iff] at hx

    have hx0 : x ≠ 0 := by
      by_contra hx0
      let h0 := zero_closure_rpow a hant harch
      rw [← hx0] at h0
      contradiction
    have hx1 : x ≠ 1 := by
      by_contra hx1
      let h1 := T.one_closure_rpow a
      rw [← hx1] at h1
      contradiction

    apply Metric.mem_closure_iff.not.mp at hx; push_neg at hx
    obtain ⟨ε, he, hx⟩ := hx
    use ⟨((x.1-(ε/2)) ⊔ 0), by
      constructor
      exact le_max_right (x.1-(ε/2)) 0
      apply max_le
      calc x.1-(ε/2)
        _ ≤ x.1-0 := by refine sub_le_sub ?_ (le_of_lt (half_pos he)); rfl
        _ = x := by ring
        _ ≤ 1 := le_one x
      exact zero_le_one
      ⟩
    use ⟨((x.1+(ε/2)) ⊓ 1), by
      constructor
      apply le_min
      apply add_nonneg (nonneg x) (le_of_lt (half_pos he))
      exact zero_le_one
      exact min_le_right (x.1+(ε/2)) 1
      ⟩
    constructor; simp only [Set.mem_Ioo]; constructor;
    apply Subtype.mk_lt_mk.mpr
    apply max_lt
    exact sub_lt_self (↑x) (half_pos he)
    exact unitInterval.pos_iff_ne_zero.mpr hx0
    apply Subtype.mk_lt_mk.mpr
    apply lt_min
    exact lt_add_of_pos_right (↑x) (half_pos he)
    exact unitInterval.lt_one_iff_ne_one.mpr hx1

    intro y hy; simp only [Set.mem_Ioo] at hy
    have hydist : dist x y < (ε/2) := by
      apply abs_sub_lt_iff.mpr; constructor
      apply And.left at hy; apply Subtype.mk_lt_mk.mp at hy
      apply sub_lt_comm.mp
      apply lt_of_le_of_lt (le_max_left (x.1-(ε/2)) 0) hy

      apply And.right at hy; apply Subtype.mk_lt_mk.mp at hy
      apply sub_left_lt_of_lt_add
      apply lt_of_lt_of_le hy (min_le_left (x.1+(ε/2)) 1)
    simp only [Set.mem_compl_iff]
    apply Metric.mem_closure_iff.not.mpr; push_neg
    use (ε/2); constructor; exact half_pos he
    intro b hb
    specialize hx b hb
    calc dist y b
      _ ≥ dist x b - dist x y := tsub_le_iff_left.mpr (dist_triangle x y b)
      _ ≥ ε - dist x y := tsub_le_tsub_right hx (dist x y)
      _ ≥ ε - (ε/2) := sub_le_sub_left (le_of_lt hydist) ε
      _ = (ε/2) := sub_half ε

theorem rpow_denseRange (harch : IsArchimedean T.toTnorm) (a : I) (hant : IsNontrivial a) : DenseRange (fun r : ℚ => T.rpow r a) := by
  by_contra! h; unfold DenseRange at h
  let D := Set.range (fun r => T.rpow r a)
  let hbasis := rpow_denseInterior harch a hant h
  obtain ⟨x, hx, p, q, hin, hsub⟩ := hbasis

  let u : I := sInf {y | (Set.Ioc y x) ⊆ (closure D)ᶜ}
  let v : I := sSup {y | (Set.Ico x y) ⊆ (closure D)ᶜ}


  have hpu : p ∈ {y | (Set.Ioc y x) ⊆ (closure D)ᶜ} := by
    rw [Set.mem_setOf]
    apply subset_trans ?_ hsub
    exact Set.Ioc_subset_Ioo_right hin.2
  have hqv : q ∈ {y | (Set.Ico x y) ⊆ (closure D)ᶜ} := by
    rw [Set.mem_setOf]
    apply subset_trans ?_ hsub
    exact Set.Ico_subset_Ioo_left hin.1

  have hinfNE : {y | (Set.Ioc y x) ⊆ (closure D)ᶜ}.Nonempty := by use p
  have hsupNE : {y | (Set.Ico x y) ⊆ (closure D)ᶜ}.Nonempty := by use q

  have he' : v > u := by
    suffices u < x ∧ x < v by
      apply lt_trans this.1 this.2
    constructor

    apply lt_of_le_of_lt ?_ hin.1
    unfold u; apply sInf_le hpu

    apply lt_of_lt_of_le hin.2
    unfold v; apply le_sSup hqv

  have hv : v ∈ closure D := by
    by_cases hv1 : v = 1
    rw [hv1]; exact one_closure_rpow a
    apply Metric.mem_closure_iff.mpr
    by_contra h
    push_neg at h
    obtain ⟨ε, he, h⟩ := h
    let w := (v+(ε/2)) ⊓ 1
    have hwI : w ∈ I := by
      constructor
      apply le_min
      apply add_nonneg (nonneg v) (le_of_lt (half_pos he))
      exact zero_le_one
      apply min_le_right
    suffices ⟨w, hwI⟩ ∈ {y | Set.Ico x y ⊆ (closure D)ᶜ} by
      have hv : w ≤ v := le_sSup this
      have hv2 : v < w := by
        apply lt_min
        apply lt_add_of_le_of_pos ?_ (half_pos he); rfl
        exact unitInterval.lt_one_iff_ne_one.mpr hv1
      apply lt_of_lt_of_le hv2 at hv
      exact (lt_self_iff_false ↑v).mp hv
    rw [Set.mem_setOf]

    intro c hc
    by_cases hcd : dist v c ≤ (ε/2)
    apply Set.mem_compl
    apply Metric.mem_closure_iff.not.mpr; push_neg
    use (ε/2); constructor; exact half_pos he
    intro b hb
    specialize h b hb
    calc dist c b
      _ ≥ dist v b - dist v c := tsub_le_iff_left.mpr (dist_triangle v c b)
      _ ≥ ε - dist v c := tsub_le_tsub_right h (dist v c)
      _ ≥ ε - (ε/2) := sub_le_sub_left hcd ε
      _ = ε/2 := sub_half ε

    push_neg at hcd
    let w' : I := ⟨((v-(ε/2)) ⊔ 0), by
      constructor
      apply le_max_right
      apply max_le
      calc v.1-(ε/2)
        _ ≤ v-0 := by refine sub_le_sub ?_ ?_; rfl; exact (le_of_lt (half_pos he))
        _ = v := by ring
        _ ≤ 1 := le_one v
      exact zero_le_one
      ⟩
    suffices c ∈ Set.Ico x w' by
      have hvw : w' < v := by
        apply Subtype.coe_lt_coe.mp
        apply max_lt
        rw [sub_lt_self_iff]
        exact half_pos he
        exact lt_of_le_of_lt (nonneg u) he'
      apply (lt_sSup_iff).mp at hvw
      obtain ⟨w'', hws, hw⟩ := hvw
      apply hws
      constructor; exact this.1
      exact lt_trans this.2 hw

    constructor; exact hc.1
    by_cases hdp : dist v c = v - c
    rw [hdp] at hcd
    apply lt_tsub_comm.mp at hcd
    apply Subtype.mk_lt_mk.mpr
    apply lt_max_iff.mpr
    left; exact hcd

    let hdp2 := abs_choice (v.1-c)
    have hdp : ¬ |v.1-c|=v.1-c := hdp
    simp only [hdp, neg_sub, false_or] at hdp2
    have hdp2 : dist v c = c - v := hdp2
    rw [hdp2] at hcd
    apply lt_tsub_iff_left.mp at hcd
    have hcd2 : c < v+(ε/2) := by
      have hasdf : w ≤ v+(ε/2) := by apply min_le_left
      have hasdf2 : c < w := by exact hc.2
      apply lt_of_lt_of_le hasdf2 hasdf
    apply lt_trans hcd at hcd2
    rw [lt_self_iff_false] at hcd2
    contradiction

  let t : ℕ → I := fun n => T.mul (T.ipow (n+1) a) v
  have htlim : Filter.Tendsto t Filter.atTop (nhds v) := by
    have hc := T.cont
    specialize hc (fun n => T.ipow (n+1) a) (fun n => v) 1 v (ipow_tendsto_one harch a hant) (tendsto_const_nhds)
    rw [T.one_mul] at hc
    exact hc
  have hmulcl : ∀ n : ℕ, (t n) ∈ closure D := by
    intro n
    suffices closure D ⊆ Set.preimage (T.mul (T.ipow (n+1) a)) (closure D) by
      apply this
      exact hv
    apply closure_minimal
    intro r hr
    rw [Set.mem_preimage]
    apply subset_closure
    by_cases hr1 : r = 1
    rw [hr1, T.mul_one]
    unfold D; rw [Set.mem_range, Tnorm.ipow_eq_rpow]
    use (1/(n+1)); push_cast; rfl
    exact Ne.symm (Nat.zero_ne_add_one n)

    unfold D at hr
    rw [Set.mem_range] at hr
    obtain ⟨s, hr⟩ := hr
    rw [← hr, Tnorm.ipow_eq_rpow, ← Tnorm.rpow_add]
    unfold D; rw [Set.mem_range]; use (1/(n+1)+s); push_cast; rfl
    exact Nat.one_div_cast_nonneg (n + 1)

    by_contra! hs
    apply le_of_lt at hs
    rw [Tnorm.zero_rpow s a hs] at hr
    symm at hr
    contradiction
    exact Ne.symm (Nat.zero_ne_add_one n)

    apply IsClosed.preimage
    refine Continuous.uncurry_left (Tnorm.ipow (n+1) a) ?_
    exact (cont_def T.toTnorm).mp T.cont
    exact isClosed_closure

  let ε := v.1-u
  have he : ε > 0 := by
    apply sub_pos.mpr
    exact he'

  apply Metric.tendsto_atTop.mp at htlim
  specialize htlim ε he
  obtain ⟨n, htlim⟩ := htlim
  specialize htlim n ?_; rfl
  specialize hmulcl n
  have htu : u < (t n) := by
    calc u.1
      _ = v.1-ε := by unfold ε; ring
      _ < (t n) := by
        apply sub_lt_comm.mp
        apply abs_sub_lt_iff.mp at htlim
        exact htlim.2
  have htv : (t n) < v := by
    apply Tnorm.mul_lt_right T (T.ipow (n+1) a) v ?_ ?_ harch
    apply And.right at hant
    contrapose! hant
    exact Tnorm.one_of_ipow_one T (n+1) hant
    apply unitInterval.pos_iff_ne_zero.mp
    apply lt_of_le_of_lt (nonneg u) (lt_add_neg_iff_lt.mp he)


  by_cases htnx : (t n) < x
  apply sInf_lt_iff.mp at htu
  obtain ⟨b, hb, hbt⟩ := htu
  rw [Set.mem_setOf] at hb
  suffices (t n) ∈ Set.Ioc b x by
    apply hb at this
    contradiction
  constructor; exact hbt;
  exact le_of_lt htnx

  push_neg at htnx
  apply lt_sSup_iff.mp at htv
  obtain ⟨b, hb, hbt⟩ := htv
  rw [Set.mem_setOf] at hb

  suffices (t n) ∈ Set.Ico x b by
    apply hb at this
    contradiction
  constructor; exact htnx
  exact hbt

lemma rpow_dense_btwn (harch : IsArchimedean T.toTnorm) (p : I) (hpnt : IsNontrivial p) (a b : I) (hab : a < b) :
  ∃ r : ℚ, a < T.rpow r p ∧ T.rpow r p < b := by
    let hd := rpow_denseRange harch p hpnt
    apply dense_iff_exists_between.mp at hd
    obtain ⟨c, hc, hcr⟩ := hd a b hab
    rw [Set.mem_range] at hc
    obtain ⟨r, hc⟩ := hc
    use r; rw [hc]; exact hcr

theorem pow_surj (hn : Nilpotent T.toTnorm) (p : I) (hpnt : IsNontrivial p) :
  Function.Surjective (T.powp p) := by
    intro b
    have hzpow : ∃ n : ℚ, T.pow n p = 0 := by
      apply And.right at hn
      specialize hn p hpnt; obtain ⟨n, hn⟩ := hn
      use n; rw [T.pow_cast, T.rpow_cast]; exact hn
    obtain ⟨n, hzpow⟩ := hzpow
    by_cases hb : b = 0
    use n; rw [hb]; exact hzpow

    let S : Set ℝ := (↑) '' {r : ℚ | T.rpow r p < b}
    let t : ℝ := sInf S
    have hbdd : BddBelow S := by
      apply bddBelow_def.mpr
      use 0; intro y hyS; unfold S at hyS
      simp only [Set.mem_image, Set.mem_setOf_eq] at hyS
      obtain ⟨y', hy, hy'⟩ := hyS
      contrapose! hy; rw [← hy'] at hy
      rw_mod_cast [Tnorm.zero_rpow y' p (le_of_lt hy)]
      exact b.2.2
    have hnonempty : S.Nonempty := by
      use n; unfold S; simp only [Set.mem_image, Set.mem_setOf_eq]
      use n; constructor; rw_mod_cast [← T.pow_cast, hzpow]
      exact unitInterval.pos_iff_ne_zero.mpr hb
      rfl
    use t; unfold powp;
    by_contra! h
    by_cases hpow : T.pow t p < b
    obtain ⟨r, hrp, hrb⟩ := rpow_dense_btwn (arch_of_nilpt T.toTnorm hn) p hpnt (T.pow t p) b hpow
    have hrS : ↑r ∈ S := by
      unfold S; simp only [Set.mem_image, Set.mem_setOf_eq, Rat.cast_inj, exists_eq_right]
      exact hrb
    have hrt : r < t := by
      contrapose! hrp
      have hasdf : T.rpow r p = T.pow r p := by rw [T.pow_cast]
      rw [hasdf]; exact pow_anti p hrp
    apply csInf_le hbdd at hrS
    apply not_le_of_lt at hrt; unfold t at hrt
    contradiction

    push_neg at hpow
    apply lt_of_le_of_ne at hpow; specialize hpow (Ne.symm h)
    obtain ⟨r, hrb, hrp⟩ := rpow_dense_btwn (arch_of_nilpt T.toTnorm hn) p hpnt b (T.pow t p) hpow
    have hrt : t < r := by
      contrapose! hrp
      have hasdf : T.rpow r p = T.pow r p := by rw [T.pow_cast]
      rw [hasdf]; exact pow_anti p hrp
    apply (csInf_lt_iff hbdd hnonempty).mp at hrt
    obtain ⟨s', hsS, hsr⟩ := hrt
    unfold S at hsS; simp only [Set.mem_image, Set.mem_setOf_eq] at hsS
    obtain ⟨s, hs, hss'⟩ := hsS
    rw [← hss'] at hsr; apply le_of_lt at hsr
    apply pow_anti p at hsr; unfold powp at hsr
    rw [T.pow_cast, T.pow_cast] at hsr
    have hbb : b < b := by
      calc b
        _ < T.rpow r p := hrb
        _ ≤ T.rpow s p := hsr
        _ < b := hs
    exact (lt_self_iff_false b).mp hbb

theorem pow_cont (hn : Nilpotent T.toTnorm) (p : I) (hpnt : IsNontrivial p) : _root_.Continuous (T.powp p) := by
  let ha := T.pow_anti p
  let hs := T.pow_surj hn p hpnt
  suffices _root_.Continuous (σ ∘ (T.powp p)) by
    apply Continuous.comp continuous_symm at this
    have hss : σ ∘ σ ∘ (T.powp p) = T.powp p := by
      ext x; simp only [Function.comp_apply, symm_symm]
    rw [← hss]; exact this
  apply Monotone.continuous_of_surjective
  intro x y hxy
  simp only [Function.comp_apply]
  apply symm_le_symm.mpr
  apply ha hxy

  apply Function.Surjective.comp ?_ hs
  refine Function.HasRightInverse.surjective ?_
  use σ; exact symm_symm


lemma sSup_pow_zero (hn : Nilpotent T.toTnorm) (p : I) (hpnt : IsNontrivial p) : T.pow (sSup {t : ℝ | T.pow t p ≠ 0}) p = 0 := by
  let hc := T.pow_cont hn p hpnt
  apply And.right at hn;
  specialize hn p hpnt; obtain ⟨n, hn⟩ := hn
  have hpz : {t | T.pow t p = 0}.Nonempty := by
    use n; rw [Set.mem_setOf_eq, ← Rat.cast_natCast, T.pow_cast, T.rpow_cast];
    exact hn
  have hclo : IsClosed {t | T.pow t p = 0} := by
    have hpp : (T.powp p) ⁻¹' {0} = {t | T.pow t p = 0} := by rfl
    rw [← hpp]
    apply IsClosed.preimage hc isClosed_singleton
  have hbdd : BddBelow {t | T.pow t p = 0} := by
    apply bddBelow_def.mpr
    use 0; intro t ht; rw [Set.mem_setOf_eq] at ht
    contrapose! ht
    apply le_of_lt at ht
    apply pow_anti p at ht; unfold powp at ht
    rw [T.pow_zero] at ht
    apply unitInterval.pos_iff_ne_zero.mp
    apply lt_of_lt_of_le zero_lt_one ht

  suffices sInf {t | T.pow t p = 0} = sSup {t | T.pow t p ≠ 0} by
    rw [← this]
    suffices sInf {t | T.pow t p = 0} ∈ {t | T.pow t p = 0} by rw [Set.mem_setOf_eq] at this; exact this
    exact IsClosed.csInf_mem hclo hpz hbdd

  refine Eq.symm (csSup_eq_of_is_forall_le_of_forall_le_imp_ge ?_ ?_ ?_)
  use 0; simp only [ne_eq, Set.mem_setOf_eq, pow_zero, one_ne_zero, not_false_eq_true]
  intro t ht; simp only [ne_eq, Set.mem_setOf_eq] at ht
  apply le_csInf hpz
  intro b hb; rw [Set.mem_setOf_eq] at hb
  apply unitInterval.pos_iff_ne_zero.mpr at ht
  rw [← hb] at ht
  contrapose! ht
  exact pow_anti p (le_of_lt ht)

  intro ub ha
  suffices ub ∈ {t | T.pow t p = 0} by exact csInf_le hbdd this
  apply isOpen_compl_iff.mpr at hclo
  by_contra h
  have h : ub ∈ {t | T.pow t p = 0 }ᶜ := h
  apply Metric.isOpen_iff.mp at hclo
  specialize hclo ub h
  obtain ⟨ε, he, hclo⟩ := hclo
  let a := ub+(ε/2)
  have hab : a ∈ Metric.ball ub ε := by
    rw [Metric.mem_ball]
    have hasd : dist a ub = |(ub+(ε/2))-ub| := by rfl
    rw [hasd, add_sub_cancel_left, abs_of_pos (half_pos he), half_lt_self_iff]
    exact he
  specialize hclo hab; specialize ha a hclo
  apply not_lt_of_le at ha
  have ha2 : ub < a := by
    unfold a;
    simp only [lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right]
    exact he
  contradiction

lemma nonzeropow_nonempty (p : I) : {t | T.pow t p ≠ 0}.Nonempty := by
  use 0; rw [Set.mem_setOf_eq]
  rw [pow_zero]; exact one_ne_zero

lemma nonzeropow_bddAbove (h : Nilpotent T.toTnorm) (p : I) (hpnt : IsNontrivial p) : BddAbove {t | T.pow t p ≠ 0} := by
  apply bddAbove_def.mpr
  apply And.right at h
  specialize h p hpnt
  obtain ⟨n, hn⟩ := h
  use n; intro t ht; rw [Set.mem_setOf_eq] at ht
  rw [← T.rpow_cast, ← T.pow_cast] at hn;
  apply unitInterval.pos_iff_ne_zero.mpr at ht
  rw[← hn] at ht
  contrapose! ht
  apply pow_anti p (le_of_lt ht)

theorem pow_inj (hn : Nilpotent T.toTnorm) (p : I) (hpnt : IsNontrivial p) :
  (Set.InjOn (T.powp p) (Set.Icc 0 (sSup {t : ℝ | T.pow t p ≠ 0}))) := by
    let hn2 := hn
    apply And.right at hn2
    specialize hn2 p hpnt
    obtain ⟨n, hn2⟩ := hn2
    rw [← T.rpow_cast] at hn2
    intro r₁ hr₁ r₂ hr₂ hpow
    simp_all only [Set.mem_Icc]
    unfold powp at hpow

    contrapose! hpow
    wlog hr12 : r₁ < r₂

    push_neg at hr12; apply lt_of_le_of_ne at hr12
    symm at hpow; specialize hr12 hpow
    specialize this hn p hpnt n hn2 hr₂ hr₁ hpow hr12
    symm at this; exact this

    symm; apply ne_of_lt
    have hq : ∃ q₁ q₂ : ℚ, r₁ ≤ q₁ ∧ q₁ < q₂ ∧ q₂ ≤ r₂ := by
      apply exists_rat_btwn at hr12
      obtain ⟨q₁, hr1, hr2⟩ := hr12
      apply exists_rat_btwn at hr2
      obtain ⟨q₂, hq1, hr2⟩ := hr2
      use q₁; use q₂; constructor; exact le_of_lt hr1
      constructor; exact_mod_cast hq1; exact le_of_lt hr2
    obtain ⟨q₁, q₂, hrq1, hq, hrq2⟩ := hq
    let hrq1' := hrq1; let hrq2' := hrq2
    apply (pow_anti p) at hrq1; apply (pow_anti p) at hrq2

    calc T.pow r₂ p
      _ ≤ T.pow q₂ p := hrq2
      _ = T.rpow q₂ p := by rw [pow_cast q₂ p]
      _ < T.rpow q₁ p := by
        apply Tnorm.rpow_strict_anti (arch_of_nilpt T.toTnorm hn)
        exact hq; exact hpnt
        apply_mod_cast le_trans hr₁.1 hrq1'
        suffices sSup ((↑) '' {t : ℚ | T.rpow t p ≠ 0}) = sSup ({t : ℝ | T.pow t p ≠ 0}) by
          rw [this]
          apply le_trans hrq2' hr₂.2

        refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
        intro x hx; simp only [ne_eq, Set.mem_image, Set.mem_setOf_eq] at hx
        obtain ⟨x', hx, hx'⟩ := hx
        push_neg at hx; rw [← pow_cast, hx'] at hx
        use x; simp only [ne_eq, Set.mem_setOf_eq, le_refl, and_true]
        exact hx

        intro y hy; rw [Set.mem_setOf_eq] at hy

        suffices y < sSup {t : ℝ | T.pow t p ≠ 0} by
          apply exists_rat_btwn at this
          obtain ⟨x, hxy, hx⟩ := this
          use x; simp only [ne_eq, Set.mem_image, Set.mem_setOf_eq, Rat.cast_inj, exists_eq_right]
          constructor; swap; exact le_of_lt hxy

          apply (lt_csSup_iff (nonzeropow_bddAbove hn p hpnt) (nonzeropow_nonempty p)).mp at hx
          obtain ⟨b, hb, hbx⟩ := hx
          rw [Set.mem_setOf_eq] at hb
          apply le_of_lt at hbx; apply pow_anti p at hbx
          apply unitInterval.pos_iff_ne_zero.mpr at hb; apply unitInterval.pos_iff_ne_zero.mp
          rw [← T.pow_cast]
          apply lt_of_lt_of_le hb hbx

        apply lt_of_le_of_ne
        apply le_csSup (nonzeropow_bddAbove hn p hpnt)
        rw [Set.mem_setOf_eq]; exact hy

        apply_fun T.powp p
        unfold powp;
        rw [sSup_pow_zero hn p hpnt]; exact hy
      _ = T.pow q₁ p := by rw [pow_cast q₁ p]
      _ ≤ T.pow r₁ p := hrq1

lemma pow_rat_seq_cont (hn : Nilpotent T.toTnorm) {t : ℝ} (p : I) (hpnt : IsNontrivial p) {u : ℕ → ℚ} :
  (Filter.Tendsto (fun n => ↑(u n)) Filter.atTop (nhds t)) → (Filter.Tendsto (fun n => T.pow (u n) p) Filter.atTop (nhds (T.pow t p))) := by
    intro h; let hc := T.pow_cont hn p hpnt
    apply continuous_iff_seqContinuous.mp at hc
    exact hc h

theorem pow_add (hn : Nilpotent T.toTnorm) (t t' : ℝ) (p : I) (hpnt : IsNontrivial p) (ht0 : t ≥ 0) (ht0' : t' ≥ 0) :
  T.pow (t+t') p = T.mul (T.pow t p) (T.pow t' p) := by
    obtain ⟨u, _, hltu, hliu⟩ := Real.exists_seq_rat_strictAnti_tendsto t
    obtain ⟨u', _, hltu', hliu'⟩ := Real.exists_seq_rat_strictAnti_tendsto t'
    let hliu₂ := pow_rat_seq_cont hn p hpnt hliu
    let hliu'₂ := pow_rat_seq_cont hn p hpnt hliu'
    let h := T.cont (fun n => T.pow (u n) p) (fun n => T.pow (u' n) p) (T.pow t p) (T.pow t' p)
      hliu₂ hliu'₂
    apply tendsto_nhds_unique ?_ h
    simp only
    have hmulpow : (fun n => T.mul (T.pow ↑(u n) p) (T.pow ↑(u' n) p)) = (fun n => T.pow ↑((u n)+(u' n)) p) := by
      ext n; simp only [T.pow_cast]; symm; apply Subtype.coe_inj.mpr
      apply Tnorm.rpow_add (u n) (u' n) p
      exact_mod_cast le_trans ht0 (le_of_lt (hltu n))
      exact_mod_cast le_trans ht0' (le_of_lt (hltu' n))
    rw [hmulpow]
    apply pow_rat_seq_cont hn p hpnt; push_cast
    have hfunc : Continuous (fun p : ℝ×ℝ => p.1+p.2) := by exact continuous_add
    apply continuous_iff_seqContinuous.mp at hfunc
    have hprodlim : Filter.Tendsto (fun n => (↑(u n), ↑(u' n))) Filter.atTop (nhds (t,t')) := by
      exact Filter.Tendsto.prodMk_nhds hliu hliu'
    apply hfunc hprodlim



end ContinuousTnorm
