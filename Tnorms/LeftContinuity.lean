import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Continuity
import Mathlib.Data.Real.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Sequences
import Mathlib.Topology.Semicontinuous
open unitInterval



section namespace Tnorm
  def LowerSemicontinuous (T : Tnorm) := ∀ p₀ q₀ : I, ∀ ε > 0, ∃ δ > 0,
  ∀ p q : I, p₀.1-δ < p → p ≤ p₀ → q₀-δ < q → q ≤ q₀ → (T.mul p₀ q₀).1-ε < T.mul p q
end Tnorm


theorem lower_semi_def (T : Tnorm) : T.LowerSemicontinuous ↔ LowerSemicontinuous (Function.uncurry T.mul) := by
  constructor
  intro h (p, q) r hr
  refine Metric.eventually_nhds_iff.mpr ?_
  simp at hr
  specialize h p q ((T.mul p q).1 - r) ?_
  simp [hr]
  obtain ⟨δ, hdp, h⟩ := h
  use δ
  constructor
  exact hdp
  intro (p', q') hdist; rw [Function.uncurry_apply_pair]
  by_cases hp : p < p'
  by_cases hq : q < q'

  apply lt_of_lt_of_le hr
  apply T.mul_le_mul p p' q q' (le_of_lt hp) (le_of_lt hq)

  push_neg at hq
  specialize h p q' ?_ ?_ ?_ hq
  exact sub_lt_self (↑p) hdp; rfl
  apply sub_lt_comm.mp
  rw [Prod.dist_eq] at hdist
  simp at hdist
  let hdist := hdist.2
  apply Metric.mem_ball'.mp at hdist
  apply lt_of_abs_lt hdist
  simp at h
  apply lt_of_lt_of_le h (T.mul_le_mul p p' q' q' (le_of_lt hp) ?_); rfl

  push_neg at hp
  by_cases hq : q < q'
  specialize h p' q ?_ hp ?_ ?_
  rw [Prod.dist_eq] at hdist
  simp at hdist
  let hdist := hdist.1
  apply Metric.mem_ball'.mp at hdist
  apply sub_lt_comm.mp
  apply lt_of_abs_lt hdist
  exact sub_lt_self (↑q) hdp; rfl
  simp at h
  apply lt_of_lt_of_le h (T.mul_le_mul p' p' q q' ?_ (le_of_lt hq)); rfl

  push_neg at hq
  rw [Prod.dist_eq] at hdist
  simp at hdist
  let h1 := hdist.1; let h2 := hdist.2
  apply Metric.mem_ball'.mp at h1; apply Metric.mem_ball'.mp at h2
  specialize h p' q' ?_ hp ?_ hq
  apply sub_lt_comm.mp
  apply lt_of_abs_lt h1
  apply sub_lt_comm.mp
  apply lt_of_abs_lt h2
  simp at h
  exact h



  intro h
  intro p₀ q₀ ε he
  by_cases h1 : ε > (T.mul p₀ q₀)
  use 1; constructor; exact Real.zero_lt_one
  intro p q hpl hpg hql hqg
  calc (T.mul p₀ q₀).1 - ε
    _ < 0 := by apply sub_neg.mpr h1
    _ ≤ T.mul p q := nonneg (T.mul p q)

  push_neg at h1
  have hmI : (T.mul p₀ q₀).1 - ε ∈ I := by
    simp
    constructor
    exact h1
    apply le_trans (le_one (T.mul p₀ q₀)); simp; exact le_of_lt he
  specialize h (p₀, q₀) ⟨(T.mul p₀ q₀).1 - ε, hmI⟩ ?_
  apply Subtype.mk_lt_mk.mpr
  simp; exact he

  apply Metric.eventually_nhds_iff.mp at h
  obtain ⟨δ, hdp, h⟩ := h
  use δ
  constructor
  exact hdp
  intro p q hpl hpg hql hqg
  have hdist : dist (p, q) (p₀, q₀) < δ := by
    rw [Prod.dist_eq]
    apply max_lt_iff.mpr
    constructor
    simp
    apply abs_sub_lt_iff.mpr
    constructor
    apply lt_of_le_of_lt ?_ hdp
    exact tsub_nonpos.mpr hpg
    apply sub_lt_comm.mp hpl

    simp
    apply abs_sub_lt_iff.mpr
    constructor
    apply lt_of_le_of_lt ?_ hdp
    exact tsub_nonpos.mpr hqg
    apply sub_lt_comm.mp hql
  specialize h hdist
  simp at h
  exact h



lemma nat_approach_mem {p : I} {n : ℕ} : (max 0 (p.1- 1/(n+1))) ∈ I := by
    simp
    calc p.1
      _ ≤ 1 := p.2.2
      _ ≤ 1+(↑n+1)⁻¹ := by
        refine le_add_of_le_of_nonneg ?_ ?_; rfl
        refine inv_nonneg.mpr ?_
        refine add_nonneg ?_ ?_
        exact Nat.cast_nonneg' n
        exact zero_le_one' ℝ

noncomputable
def nat_approach (p : I) := ((fun n => ⟨0 ⊔ (p.1-(1/(n+1))), nat_approach_mem⟩) : ℕ → I)

lemma nat_approach_mono {p : I} : Monotone (nat_approach p) := by
  intro n m hnm
  apply Subtype.mk_le_mk.mpr
  apply max_le_iff.mpr
  constructor
  apply le_max_left
  apply le_max_of_le_right
  refine sub_le_sub ?_ ?_; rfl
  exact Nat.one_div_le_one_div hnm

lemma nat_approach_lim {p : I} : Filter.Tendsto (nat_approach p) Filter.atTop (nhds p) := by
  apply Metric.tendsto_atTop.mpr
  intro ε he
  let hN := Real.instArchimedean.arch
  specialize hN 1 he
  obtain ⟨N, hN⟩ := hN
  use N
  intro n hn
  apply max_lt_iff.mpr
  constructor
  apply sub_left_lt_of_lt_add
  apply max_lt_iff.mpr
  constructor
  refine add_pos_of_nonneg_of_pos (nonneg p) he
  calc p.1-(1/(n+1))
    _ ≤ p := by
        refine tsub_le_iff_tsub_le.mp ?_; simp;
        refine add_nonneg ?_ ?_
        exact Nat.cast_nonneg' n
        exact zero_le_one' ℝ
    _ < p+ε := by exact lt_add_of_pos_right (↑p) he

  simp
  calc p.1 - (nat_approach p n)
    _ ≤ p.1-(p-(1/(n+1))) := by refine sub_le_sub ?_ ?_; rfl; apply le_max_right
    _ = 1/(n+1) := by ring
    _ ≤ 1/(N+1) := by exact Nat.one_div_le_one_div hn
    _ < ε := by
      refine (div_lt_iff₀' ?_).mpr ?_
      exact Nat.cast_add_one_pos N
      simp at hN
      calc 1
        _ ≤ N*ε := by exact hN
        _ < (N+1)*ε := by linarith



theorem left_cont_lower_semi (T : Tnorm) : T.LeftContinuous ↔ T.LowerSemicontinuous := by
    constructor
    intro h p₀ q₀ ε he
    let x : ℕ → I := nat_approach p₀
    let y : ℕ → I := nat_approach q₀

    specialize h x y p₀ q₀ nat_approach_mono nat_approach_mono nat_approach_lim nat_approach_lim
    apply Metric.tendsto_atTop.mp at h
    specialize h ε he
    obtain ⟨N, h⟩ := h
    use 1/(N+1)
    constructor
    exact Nat.one_div_pos_of_nat
    intro p q hpl hpg hql hqg
    specialize h N ?_
    rfl
    apply sub_lt_comm.mp
    calc (T.mul p₀ q₀).1 - (T.mul p q)
      _ ≤ (T.mul p₀ q₀) - (T.mul (x N) (y N)) := by
            apply sub_le_sub_left
            apply T.mul_le_mul

            by_cases hxn : p₀.1- (1/(N+1)) ≤ 0
            apply max_eq_left at hxn
            apply Subtype.mk_le_mk.mpr
            rw [hxn]; exact nonneg p
            apply lt_of_not_le at hxn
            apply le_of_lt at hxn
            apply max_eq_right at hxn
            apply Subtype.mk_le_mk.mpr
            rw [hxn]
            apply le_of_lt
            exact_mod_cast hpl


            by_cases hyn : q₀.1- (1/(N+1)) ≤ 0
            apply max_eq_left at hyn
            apply Subtype.mk_le_mk.mpr
            rw [hyn]; exact nonneg q
            apply lt_of_not_le at hyn
            apply le_of_lt at hyn
            apply max_eq_right at hyn
            apply Subtype.mk_le_mk.mpr
            rw [hyn]
            apply le_of_lt
            exact_mod_cast hql
      _ ≤ |(T.mul p₀ q₀).1 - (T.mul (x N) (y N))| := by apply le_abs_self
      _ = |(T.mul (x N) (y N)).1 - (T.mul p₀ q₀)| := by apply abs_sub_comm
      _ < ε := by exact h


    intro h
    intro x y p q hxm hym hxl hyl
    apply Metric.tendsto_atTop.mpr
    let hxl2 := hxl; let hyl2 := hyl
    apply Metric.tendsto_atTop.mp at hxl; apply Metric.tendsto_atTop.mp at hyl
    intro ε he
    specialize h p q ε he
    obtain ⟨δ, hd, h⟩ := h
    specialize hxl δ hd; specialize hyl δ hd

    obtain ⟨Nx, hxl⟩ := hxl; obtain ⟨Ny, hyl⟩ := hyl
    use max Nx Ny
    intro n hn
    specialize hxl n (le_of_max_le_left hn); specialize hyl n (le_of_max_le_right hn)
    specialize h (x n) (y n) (sub_lt_of_abs_sub_lt_left hxl)

    have hxb : (x n) ≤ p := by exact Monotone.ge_of_tendsto hxm hxl2 n
    have hyb : (y n) ≤ q := by exact Monotone.ge_of_tendsto hym hyl2 n

    specialize h hxb (sub_lt_of_abs_sub_lt_left hyl) hyb

    apply max_lt_iff.mpr
    constructor
    calc (T.mul (x n) (y n)).1 - (T.mul p q)
      _ ≤ 0 := by refine tsub_nonpos_of_le ?_; apply T.mul_le_mul; exact hxb; exact hyb
      _ < ε := he

    rw [neg_sub]
    apply sub_lt_comm.mp
    exact h

theorem left_cont_sup (T : LeftContinuousTnorm) (S : Set I) : ∀ q : I,
  sSup (Set.range (fun (s : S) => T.mul s q))
  = T.mul (sSup S) q := by
    intro q
    by_cases hs : S.Nonempty
    swap
    push_neg at hs
    conv => rhs
            rw [hs]
    simp
    have h : Set.range (fun (s : S) => T.mul s q) = ∅ := by
      simp only [Set.range_eq_empty_iff, hs, Set.isEmpty_coe_sort]
    rw [h]
    have hbot : (⊥ : I) = 0 := rfl
    rw [sSup_empty, hbot, T.zero_mul]



    refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
    intro b hb
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_Icc] at hb
    obtain ⟨a, hbI, haS, hb, _⟩ := hb
    apply T.mul_le_mul_right
    exact le_sSup haS

    intro w h
    let ε := (T.mul (sSup S) q).1-w
    have he : ε > 0 := by exact sub_pos.mpr h
    let hT := T.left_cont
    apply (left_cont_lower_semi T.toTnorm).mp at hT
    specialize hT (sSup S) q ε he
    obtain ⟨δ, hd, hT⟩ := hT
    have ha : ∃ a ∈ S, (sSup S)+(-δ) < a := by
      apply (UnitInterval.le_sSup_iff hs).mp; rfl
      exact neg_neg_iff_pos.mpr hd
    obtain ⟨a, haS, har⟩ := ha
    let haS2 := haS
    specialize hT a q har (le_sSup haS2)
    specialize hT ?_ ?_
    simp only [sub_lt_self_iff, hd]; rfl

    unfold ε at hT; simp only [sub_sub_cancel, Subtype.coe_lt_coe] at hT
    use (T.mul a q); constructor;
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_Icc]
    use a; use a.2; exact hT


lemma max_del_mem {p : I} {δ : ℝ} (h : δ > 0) : (max 0 (p - (δ/2))) ∈ I := by
    simp
    calc p.1
    _ ≤ 1 := by exact le_one p
    _ ≤ 1+(δ/2) := by refine le_add_of_le_of_nonneg ?_ ?_; rfl; apply le_of_lt; apply half_pos; exact h

theorem left_cont_one_var_iff_lower_semi (T : Tnorm) : (∀ p q : I, ∀ ε > 0, ∃ δ > 0,
  ∀ r : I, p.1-δ < r → r ≤ p → |(T.mul r q).1-(T.mul p q)| < ε) ↔ T.LowerSemicontinuous := by
    constructor; intro h p₀ q₀ ε he

    let h00 := h p₀ q₀ (ε/2) (half_pos he)
    obtain ⟨δ₁, hd1p, hd1⟩ := h00
    let p₁ : I := ⟨max 0 (p₀-(δ₁/2)), max_del_mem hd1p⟩

    specialize h q₀ p₁ (ε/2) (half_pos he)
    obtain ⟨δ₂, hd2⟩ := h
    obtain ⟨hd2p, hd2⟩ := hd2
    let q₁ : I := ⟨max 0 (q₀-(δ₂/2)), max_del_mem hd2p⟩

    let δ := min (δ₁/2) (δ₂/2)
    use δ; constructor
    exact lt_min (half_pos hd1p) (half_pos hd2p)

    intro p q
    intro hpl hpg hql hqg

    have hmul : (T.mul p₁ q₁).1 ≤ T.mul p q := by
      apply T.mul_le_mul p₁ p q₁ q
      apply Subtype.coe_le_coe.mp
      apply max_le_iff.mpr
      constructor
      exact nonneg p
      calc p₀ - (δ₁/2)
        _ ≤ p₀ - δ := by refine tsub_le_tsub ?_ ?_; rfl; exact min_le_left (δ₁/2) (δ₂/2)
        _ ≤ p := by apply le_of_lt hpl
      apply Subtype.coe_le_coe.mp
      apply max_le_iff.mpr
      constructor
      exact nonneg q
      calc q₀ - (δ₂/2)
        _ ≤ q₀ - δ := by refine tsub_le_tsub ?_ ?_; rfl; exact min_le_right (δ₁/2) (δ₂/2)
        _ ≤ q := by apply le_of_lt hql

    have hin : |(T.mul p₀ q₀).1 - (T.mul p₁ q₁)| < ε := by
      have hp1l : p₀ - δ₁ < p₁.1 := by
        apply lt_max_iff.mpr
        right
        simp only [sub_lt_sub_iff_left, half_lt_self_iff, hd1p]
      have hp1g : p₁.1 ≤ p₀ := by
        apply max_le_iff.mpr
        simp
        constructor
        exact nonneg p₀
        apply half_pos at hd1p
        exact le_of_lt hd1p
      have hq1l : q₀ - δ₂ < q₁.1 := by
        apply lt_max_iff.mpr
        right
        simp [hd2p]
      have hq1g : q₁.1 ≤ q₀ := by
        apply max_le_iff.mpr
        simp
        constructor
        exact nonneg q₀
        apply half_pos at hd2p
        exact le_of_lt hd2p

      specialize hd1 p₁ hp1l hp1g
      specialize hd2 q₁ hq1l hq1g
      rw [← abs_neg, neg_sub] at hd1
      nth_rw 1 [T.mul_comm] at hd2; nth_rw 2 [T.mul_comm] at hd2
      rw [← abs_neg, neg_sub] at hd2

      calc |(T.mul p₀ q₀).1 - (T.mul p₁ q₁)|
        _ ≤ |(T.mul p₀ q₀).1 - (T.mul p₁ q₀)|+|(T.mul p₁ q₀).1-(T.mul p₁ q₁)| := by exact abs_sub_le (T.mul p₀ q₀).1 (T.mul p₁ q₀) (T.mul p₁ q₁)
        _ < ε/2 + |(T.mul p₁ q₀).1-(T.mul p₁ q₁)| := by exact (add_lt_add_iff_right |(T.mul p₁ q₀).1 - (T.mul p₁ q₁)|).mpr hd1
        _ < ε/2 + ε/2 := by exact (add_lt_add_iff_left (ε/2)).mpr hd2
        _ = ε := by rw [add_halves]

    calc (T.mul p₀ q₀).1 - ε
      _ < T.mul p₁ q₁ := by exact sub_lt_of_abs_sub_lt_right hin
      _ ≤ T.mul p q := by exact hmul



    intro h p q ε he
    specialize h p q ε he
    obtain ⟨δ, hdp, hmul⟩ := h
    use δ; constructor; exact hdp
    intro r hrl hrg
    rw [abs_eq_max_neg]
    apply max_lt

    apply T.mul_le_mul_right r p at hrg
    specialize hrg q
    apply sub_lt_iff_lt_add.mpr
    calc (T.mul r q).1
      _ ≤ (T.mul p q) := by exact hrg
      _ < ε+(T.mul p q) := by exact lt_add_of_pos_left (↑(T.mul p q)) he

    rw [neg_sub]
    specialize hmul r q hrl hrg ?_ ?_
    rw [sub_lt_self_iff]; exact hdp
    rfl; exact sub_lt_comm.mp hmul
