import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Examples
import Tnorms.Algebra
import Tnorms.LeftContinuity
import Tnorms.Continuity
import Tnorms.LeftContinuousArchimedean

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Data.Real.Basic

open unitInterval

section namespace Tnorm

variable {T : Tnorm}

noncomputable
def ipow (n : ℕ) (p : I) : I := sSup ({q : I | T.npow n q < p})

noncomputable
def rpow (r : ℚ) (p : I) := T.npow r.num.toNat (T.ipow r.den p)

@[simp] lemma ipow_nat_one (p : I) : T.ipow 1 p = p := by
  unfold ipow
  by_cases hp : p = 0
  rw [hp]
  have hs : {q : I | T.npow 1 q < 0} = ∅ := by simp only [npow_one, not_lt_zero', Set.setOf_false]
  rw [hs]
  rw [sSup_empty]; rfl

  push_neg at hp
  apply unitInterval.pos_iff_ne_zero.mpr at hp
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  intro a ha; rw [Set.mem_setOf] at ha
  rw [T.npow_one] at ha
  exact le_of_lt ha

  intro w hw
  obtain ⟨q, hwq, hqp⟩ := exists_between hw
  use q; constructor
  rw [Set.mem_setOf, T.npow_one]; exact hqp
  exact hwq

@[simp] lemma ipow_nat_zero (p : I) : T.ipow 0 p = 0 := by
  unfold ipow
  have h : {q : I | T.npow 0 q < p} = ∅ := by
    refine Set.eq_empty_of_forall_notMem ?_
    simp only [npow_zero, Set.mem_setOf_eq, not_lt, forall_const]
    exact le_one p
  rw [h]
  apply sSup_empty

@[simp] lemma ipow_I_zero (n : ℕ) : T.ipow n 0 = 0 := by
  unfold ipow
  have h : {q : I | T.npow n q < 0} = ∅ := by simp only [not_lt_zero', Set.setOf_false]
  rw [h, sSup_empty]; rfl


lemma rpow_cast (n : ℕ) (p : I) : T.rpow n p = T.npow n p := by unfold rpow; simp only [Rat.num_natCast,
  Int.toNat_natCast, Rat.den_natCast, ipow_nat_one]

lemma npow_ne_zero_zero (n : ℕ) (h : n ≠ 0) : T.npow n 0 = 0 := by
  induction' n with n ih
  simp; exact h rfl
  by_cases hn : n = 0
  rw [hn]; simp
  specialize ih hn
  rw [T.npow_succ, ih, T.mul_zero]


lemma ipow_le (n : ℕ) {p q : I} : p ≤ q → T.ipow n p ≤ T.ipow n q := by
  intro hpq
  by_cases hn : n = 0
  rw [hn, T.ipow_nat_zero, T.ipow_nat_zero]

  by_cases hp : p = 0
  rw [hp, T.ipow_I_zero]
  exact nonneg (T.ipow n q)

  unfold ipow
  apply unitInterval.pos_iff_ne_zero.mpr at hp
  apply sSup_le_sSup

  intro r hr
  simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Set.mem_Icc, exists_and_right, exists_eq_right]
  simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Set.mem_Icc, exists_and_right, exists_eq_right] at hr
  apply lt_of_lt_of_le hr hpq

variable {T : ContinuousTnorm}

lemma lt_of_npow_lt (T : Tnorm) (n : ℕ) (p q : I) : T.npow n p < T.npow n q → p < q := by
  contrapose!
  exact T.npow_le n q p

theorem npow_cont (T : ContinuousTnorm) (n : ℕ) : _root_.Continuous (T.npow n) := by
  apply continuous_iff_seqContinuous.mpr
  intro x p hx
  induction' n with n ih
  apply tendsto_const_nhds

  simp at ih
  let y : ℕ → I := (fun m => T.npow n (x m))
  let h := T.cont x y p (T.npow n p) hx ih
  exact h

lemma npow_uni_cont (T : ContinuousTnorm) (n : ℕ) : UniformContinuous (T.npow n) := by
  exact CompactSpace.uniformContinuous_of_continuous (npow_cont T n)

theorem pow_inv (T : ContinuousTnorm) (n : ℕ) (p : I) (h : n ≠ 0) : T.npow n (T.ipow n p) = p := by
  unfold ipow
  by_cases hp : p = 0

  have hemp : {q : I | T.npow n q < p} = ∅ := by
    refine Set.subset_empty_iff.mp ?_
    intro q; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, imp_false, not_lt]
    rw [hp]; exact (T.npow n q).2.1
  have hempz : sSup {q : I | T.npow n q < p} = (0 : I) := by rw [hemp, sSup_empty]; rfl
  rw [hempz, T.npow_ne_zero_zero n h, hp]


  let r : I := sInf {q | T.npow n q = p}
  have hrp : T.npow n r = p := by
    have hrp : r ∈ {q | T.npow n q = p} := by
      unfold r
      refine IsClosed.sInf_mem ?_ (isClosed_eq (npow_cont T n) continuous_const)

      have her : ∃ q : I, T.npow n q = p := by
        let h2 := intermediate_value_univ 0 1 (npow_cont T n)
        rw [T.npow_ne_zero_zero n h, T.npow_I_one n] at h2
        exact h2 p.2
      obtain ⟨q, hq⟩ := her
      use q; rw [Set.mem_setOf]; exact hq

    rw [Set.mem_setOf] at hrp; exact hrp

  suffices sSup {q | T.npow n q < p} = r by
    rw [this, hrp]

  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt

  intro a ha; rw [Set.mem_setOf] at ha
  rw [← hrp] at ha
  apply lt_of_npow_lt at ha
  exact le_of_lt ha

  intro w hwr
  obtain ⟨a, hwa, har⟩ := exists_between hwr
  use a; constructor; swap; exact hwa
  rw [Set.mem_setOf]
  contrapose! har
  by_cases harar : r ≤ a
  exact harar

  apply sInf_le; rw [Set.mem_setOf]
  apply antisymm ?_ har
  rw [← hrp]
  apply T.npow_le n
  push_neg at harar
  exact le_of_lt harar

theorem ipow_mul (n m : ℕ) (p : I) : T.ipow n (T.ipow m p) = T.ipow (n*m) p := by
  by_cases hp : p = 0
  rw [hp, ipow_I_zero, ipow_I_zero, ipow_I_zero]
  apply unitInterval.pos_iff_ne_zero.mpr at hp
  by_cases hm : m = 0
  rw [hm, ipow_nat_zero, ipow_I_zero, Nat.mul_zero, ipow_nat_zero]

  unfold ipow
  have hnempty : {q | T.npow m q < p}.Nonempty := by
    use 0; rw [Set.mem_setOf, npow_ne_zero_zero m hm]; exact hp

  refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
  intro x hx; rw [Set.mem_setOf] at hx
  use x
  constructor; swap; rfl
  rw [Set.mem_setOf]
  apply lt_sSup_iff.mp at hx
  obtain ⟨q, hq, hpow⟩ := hx
  rw [Set.mem_setOf] at hq
  calc T.npow (n*m) x
    _ = T.npow m (T.npow n x) := by rw [T.npow_mul, Nat.mul_comm]
    _ ≤ T.npow m q := by apply T.npow_le; exact le_of_lt hpow
    _ < p := hq

  intro x hx; rw [Set.mem_setOf] at hx
  use x; constructor; swap; rfl; rw [Set.mem_setOf]
  have hr : sSup {q | T.npow m q < p} = T.ipow m p := by rfl
  rw [hr]
  by_contra h; push_neg at h
  apply T.npow_le m at h
  rw [pow_inv T m p hm, T.npow_mul, Nat.mul_comm] at h
  apply not_le_of_lt at hx
  contradiction

theorem rpow_well_defined {m n : ℕ} {r : ℚ} {p : I} (hnz : n ≠ 0) : r.num * n = r.den * m → T.rpow r p = T.npow m (T.ipow n p) := by
  intro h
  unfold rpow
  have hm : ∃ k : ℕ, m = k*(r.num.toNat) ∧ n = k * r.den ∧ k ≠ 0 := by
    have hrnumnn : r.num ≥ 0 := by
      apply Nat.pos_iff_ne_zero.mpr at hnz
      have hnz : 0 < (n : ℤ) := by exact_mod_cast hnz
      apply nonneg_of_mul_nonneg_left ?_ hnz
      rw [h]
      exact Lean.Omega.Int.ofNat_mul_nonneg
    have hdvd : r.den ∣ n := by
      have hcond : r.den.Coprime r.num.natAbs := Nat.coprime_comm.mp r.reduced
      apply (Nat.Coprime.dvd_mul_left hcond).mp
      use m
      rw [← Int.natAbs_of_nonneg hrnumnn] at h
      exact_mod_cast h
    obtain ⟨k, hdvd⟩ := hdvd
    use k
    constructor
    have hm : ↑m = k * r.num := by
      apply nat_mul_inj' ?_ r.den_nz
      calc ↑(r.den) * ↑m
        _ = r.num * (r.den * k) := by rw_mod_cast [← h, hdvd]
        _ = r.den * (k*r.num) := by ring
    rw [← Int.toNat_of_nonneg hrnumnn ] at hm
    exact_mod_cast hm

    constructor
    rw [hdvd, Nat.mul_comm]
    by_contra hk
    rw [hk, Nat.mul_zero] at hdvd
    contradiction
  obtain ⟨k, hm, hn, hk⟩ := hm
  rw [hm, Nat.mul_comm, ← T.npow_mul]
  rw [hn, ← ipow_mul, pow_inv]
  exact hk

theorem rpow_add (r s : ℚ) (p : I) (hr : r ≥ 0) (hs : s ≥ 0) : T.rpow (r+s) p = T.mul (T.rpow r p) (T.rpow s p) := by
  apply Rat.num_nonneg.mpr at hr; apply Rat.num_nonneg.mpr at hs
  have nonneg1 := Int.mul_nonneg hr (Int.ofNat_zero_le s.den)
  have nonneg2 := Int.mul_nonneg hs (Int.ofNat_zero_le r.den)
  have nd_nonneg : (r.num*s.den + s.num*r.den).toNat = r.num*s.den + s.num*r.den := by
    rw [Int.toNat_of_nonneg (Int.add_nonneg nonneg1 nonneg2)]
  have h : T.rpow (r+s) p = T.npow (r.num*s.den + s.num*r.den).toNat ( T.ipow (r.den * s.den) p) := by
    apply rpow_well_defined (Nat.mul_ne_zero r.den_nz s.den_nz)
    rw [nd_nonneg]
    calc (r+s).num * (r.den * s.den)
      _ = (r+s).num * r.den * s.den := by ring
      _ = (r.num * s.den + s.num * r.den) * (r+s).den := by apply Rat.add_num_den' r s
      _ = (r+s).den * (r.num * s.den + s.num * r.den) := by ring
  have nd_add := Int.toNat_add nonneg1 nonneg2
  have hrp : T.rpow r p = T.npow (r.num*s.den).toNat (T.ipow (r.den*s.den) p) := by
    apply rpow_well_defined (Nat.mul_ne_zero r.den_nz s.den_nz)
    rw [Int.toNat_of_nonneg nonneg1]
    push_cast; ring
  have hsp : T.rpow s p = T.npow (s.num*r.den).toNat (T.ipow (r.den*s.den) p) := by
    apply rpow_well_defined (Nat.mul_ne_zero r.den_nz s.den_nz)
    rw [Int.toNat_of_nonneg nonneg2]
    push_cast; ring
  rw [h, nd_add, ← T.npow_add, hrp, hsp]

lemma zero_rpow (r : ℚ) (p : I) (hr : r ≤ 0) : T.rpow r p = 1 := by
  unfold rpow
  have hnum : r.num.toNat = 0 := Int.toNat_of_nonpos (Rat.num_nonpos.mpr hr)
  rw [hnum]; apply T.npow_zero

theorem rpow_le_self (T : ContinuousTnorm) (r s : ℚ) (p : I) (h : s ≤ r) : T.rpow r p ≤ T.rpow s p := by
  by_cases hs : s < 0
  apply le_of_lt at hs
  rw [zero_rpow s p hs]; unit_interval

  push_neg at hs
  calc T.rpow r p
    _ = T.rpow (s+(r-s)) p := by rw [add_sub_cancel]
    _ = T.mul (T.rpow s p) (T.rpow (r-s) p) := rpow_add s (r-s) p hs ((Rat.le_iff_sub_nonneg s r).mp h)
    _ ≤ T.rpow s p := T.mul_le_left (T.rpow s p) (T.rpow (r-s) p)


lemma mul_lt_right (T : ContinuousTnorm) (p q : I) (hp : p ≠ 1) (hq : q ≠ 0) (h : IsArchimedean T.toTnorm) : T.mul p q < q := by
  apply nilpt_or_strict_of_cont_arch T.toTnorm T.cont at h
  rcases h with h|h
  by_cases hp0 : p = 0
  rw [hp0, T.zero_mul]
  apply unitInterval.pos_iff_ne_zero.mpr hq

  apply lt_of_le_of_ne (Tnorm.mul_le_right p q)
  by_contra! hmul
  have hpow : ∀ n : ℕ, T.mul (T.npow n p) q = q := by
    intro n; induction' n with n ih
    simp only [Tnorm.npow_zero, Tnorm.one_mul]
    rw [T.npow_succ, T.mul_assoc, ih, hmul]
  apply And.right at h
  have hpnt : IsNontrivial p := by
    constructor; exact hp0; exact hp
  specialize h p hpnt
  obtain ⟨n, hn⟩ := h
  specialize hpow n
  rw [hn, T.zero_mul] at hpow
  symm at hpow
  contradiction

  apply And.right at h
  specialize h q (unitInterval.pos_iff_ne_zero.mpr hq) p 1 (unitInterval.lt_one_iff_ne_one.mpr hp)
  rw [T.mul_comm, T.mul_one] at h
  exact h

theorem npow_strict (T : ContinuousTnorm) (harch : IsArchimedean T.toTnorm) (n m : ℕ) (p : I) (hpnt : IsNontrivial p) :
  T.npow n p ≠ 0 → n < m → T.npow m p < T.npow n p := by
    intro hz hnm
    induction' m with m ih
    contradiction

    by_cases hm : n = m
    rw [hm] at hz
    rw [hm, T.npow_succ]
    apply mul_lt_right
    exact hpnt.2; exact hz; exact harch

    push_neg at hm
    have hnm2 : n < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hnm) hm
    specialize ih hnm2
    apply lt_of_le_of_lt ?_ ih
    apply T.npow_le_self m (m+1) p
    exact Nat.le_add_right m 1

theorem npow_inj (T : ContinuousTnorm) (harch : IsArchimedean T.toTnorm) (n m : ℕ) (p : I) (hpnt : IsNontrivial p) :
  T.npow n p ≠ 0 → T.npow n p = T.npow m p → n = m := by
    intro hz h; contrapose! h
    wlog hnm : n < m
    symm at h; push_neg at hnm;
    let hm0 := hnm
    apply unitInterval.pos_iff_ne_zero.mpr at hz
    apply T.npow_le_self m n p at hm0
    apply lt_of_lt_of_le hz at hm0; apply unitInterval.pos_iff_ne_zero.mp at hm0
    specialize this T harch m n p hpnt hm0 h (lt_of_le_of_ne hnm h)
    symm; exact this

    symm; apply ne_of_lt
    apply npow_strict T harch n m p hpnt hz hnm

lemma rpow_div_one (r : ℚ) (n : ℕ) (p : I) (hn : n ≠ 0) : T.rpow r p = T.npow (r.num.toNat*n) (T.ipow (r.den*n) p) := by
  by_cases hr : r < 0
  apply le_of_lt at hr
  let hrn := Rat.num_nonpos.mpr hr
  apply Int.toNat_of_nonpos at hrn
  rw [zero_rpow r p hr, hrn, Nat.zero_mul, T.npow_zero]

  push_neg at hr
  apply rpow_well_defined
  exact Nat.mul_ne_zero r.den_nz hn
  rw [← Rat.num_nonneg] at hr
  push_cast
  rw [Int.toNat_of_nonneg hr]
  ring


lemma nonneg_of_nontrivial (r : ℚ) (p : I) : IsNontrivial (T.rpow r p) → r.num > 0 := by
  contrapose!; intro h; apply Rat.num_nonpos.mp at h
  unfold IsNontrivial; push_neg; intro h2
  exact zero_rpow r p h

lemma nontrivial_npow (n : ℕ) (p : I) (hn : n ≠ 0) : IsNontrivial (T.npow n p) → IsNontrivial p := by
  unfold IsNontrivial; contrapose!; intro hp hpow
  by_cases h0 : p = 0
  rw [h0, T.npow_ne_zero_zero n hn] at hpow
  contradiction
  specialize hp h0; rw [hp, T.npow_I_one]

theorem rpow_inj (T : ContinuousTnorm) (harch : IsArchimedean T.toTnorm) (r s : ℚ) (p : I) : IsNontrivial (T.rpow r p) → T.rpow r p = T.rpow s p → r = s := by
  intro hrnt hpow
  have hrp : r.num > 0 := nonneg_of_nontrivial r p hrnt
  have hsp : s.num ≥ 0 := by
    rw [hpow] at hrnt
    exact le_of_lt (nonneg_of_nontrivial s p hrnt)
  rw [rpow_div_one r (s.den) p s.den_nz, rpow_div_one s (r.den) p r.den_nz] at hpow
  rw [rpow_div_one r s.den p s.den_nz, Nat.mul_comm r.den s.den] at hrnt
  nth_rw 2 [Nat.mul_comm] at hpow
  apply npow_inj T harch at hpow

  refine Rat.eq_iff_mul_eq_mul.mpr ?_
  rw_mod_cast [← Int.toNat_of_nonneg (le_of_lt hrp), ← Int.toNat_of_nonneg hsp]
  exact_mod_cast hpow

  apply nontrivial_npow (r.num.toNat*s.den) (T.ipow (s.den*r.den) p) ?_ hrnt
  refine Nat.mul_ne_zero ?_ ?_
  apply Int.toNat_eq_zero.not.mpr; push_neg
  exact hrp; exact s.den_nz

  exact hrnt.1

lemma zero_rpow_iff (r : ℚ) (p : I) (hpnt : IsNontrivial p) : r ≤ 0 ↔ T.rpow r p = 1 := by
  constructor; exact zero_rpow r p
  contrapose!; intro hr
  apply unitInterval.lt_one_iff_ne_one.mp
  unfold rpow
  suffices T.ipow r.den p < 1 by
    apply lt_of_le_of_lt ?_ this
    nth_rw 2 [← T.npow_one (T.ipow r.den p)]
    apply T.npow_le_self
    refine (Int.le_toNat ?_).mpr ?_
    apply Rat.num_nonneg.mpr (le_of_lt hr)
    suffices 0 < r.num by exact this
    apply Rat.num_pos.mpr hr

  unfold ipow
  let hc := npow_cont T r.den
  apply Metric.continuous_iff.mp at hc
  specialize hc 1 (1-p) ?_
  simp only [gt_iff_lt, sub_pos, coe_lt_one]; exact unitInterval.lt_one_iff_ne_one.mpr hpnt.2
  obtain ⟨δ, hd, hc⟩ := hc
  have hq : 0 ⊔ (1-(δ/2)) < 1 := by
    apply max_lt zero_lt_one
    simp only [sub_lt_self_iff, Nat.ofNat_pos, div_pos_iff_of_pos_right]; exact hd
  let q : I := ⟨0 ⊔ (1-(δ/2)), by
    constructor; exact le_max_left 0 (1 - δ / 2)
    exact le_of_lt hq
    ⟩
  specialize hc q ?_

  apply abs_sub_lt_iff.mpr; constructor
  apply lt_trans ?_ hd
  simp only [Set.Icc.coe_one, sub_neg, coe_lt_one]
  exact hq

  apply sub_lt_comm.mp
  apply lt_max_of_lt_right
  simp only [Set.Icc.coe_one, sub_lt_sub_iff_left, half_lt_self_iff]; exact hd


  rw [T.npow_I_one] at hc
  suffices sSup {q : I | T.npow r.den q < p} ≤ q by exact lt_of_le_of_lt this hq

  obtain ⟨hp0, hp1⟩ := hpnt
  apply unitInterval.pos_iff_ne_zero.mpr at hp0; apply unitInterval.lt_one_iff_ne_one.mpr at hp1

  apply sSup_le
  intro b hb; rw [Set.mem_setOf] at hb
  have hl : T.npow r.den b < T.npow r.den q := by
    apply lt_trans hb
    apply symm_lt_symm.mp
    calc 1-(T.npow r.den q).1
      _ ≤ |1-(T.npow r.den q).1| := by apply le_abs_self
      _ = |(T.npow r.den q).1-1| := by apply abs_sub_comm
      _ < 1-p.1 := hc
  contrapose! hl
  apply T.npow_le
  exact le_of_lt hl

theorem rpow_strict_anti (harch : IsArchimedean T.toTnorm) (r s : ℚ) (p : I) (hrs : s < r) (hpnt : IsNontrivial p) :
  s ≥ 0 → r ≤ sSup ((↑) '' ({ t : ℚ | T.rpow t p ≠ 0}) : Set ℝ) → T.rpow r p < T.rpow s p := by
  intro hs hr
  apply lt_of_le_of_ne
  exact rpow_le_self T r s p (le_of_lt hrs)

  contrapose! hrs

  by_cases hrp0 : T.rpow r p = 0
  rw [hrp0] at hrs; symm at hrs
  suffices sSup (((↑) '' {t | T.rpow t p ≠ 0}) : Set ℝ) ≤ s by
    exact_mod_cast le_trans hr this
  apply csSup_le
  use 0; simp only [ne_eq, Set.mem_image, Set.mem_setOf_eq, Rat.cast_eq_zero, exists_eq_right]
  push_neg;
  have hrnpow : T.rpow 0 p = T.npow 0 p := by rfl
  rw [hrnpow, T.npow_zero]
  simp only [ne_eq, one_ne_zero, not_false_eq_true]

  intro x hx; simp only [ne_eq, Set.mem_image, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, hx⟩ := hx; push_neg at ht
  apply unitInterval.pos_iff_ne_zero.mpr at ht
  rw [← hx]; apply Rat.cast_le.mpr
  by_contra!
  apply le_of_lt at this
  apply rpow_le_self T t s p at this
  rw [hrs] at this
  apply not_lt_of_ge at this
  contradiction


  by_cases hrp1 : T.rpow r p = 1
  rw [hrp1] at hrs; symm at hrs
  apply (zero_rpow_iff r p hpnt).mpr at hrp1
  exact le_trans hrp1 hs


  apply le_of_eq
  apply rpow_inj T harch r s p ?_ hrs

  constructor
  exact hrp0
  exact hrp1

lemma ipow_eq_rpow (n : ℕ) (p : I) (h : n ≠ 0) : T.ipow n p = T.rpow (1/n) p := by
  unfold rpow
  simp [h]
  have hn : (n:ℤ).sign.toNat = 1 := by
    rw [Int.sign_natCast_of_ne_zero h]; rfl
  rw [hn, T.npow_one]

lemma ipow_le_self (T : ContinuousTnorm) {n m : ℕ} (p : I) (hn : n ≠ 0) : n ≤ m → T.ipow n p ≤ T.ipow m p := by
  intro hnm
  apply Nat.zero_lt_of_ne_zero at hn
  rw [ipow_eq_rpow, ipow_eq_rpow];
  have hnm2 : (1:ℚ)/m ≤ 1/n := one_div_le_one_div_of_le (Nat.cast_pos'.mpr hn) (Nat.cast_le.mpr hnm)
  exact rpow_le_self T ((1:ℚ)/n) ((1:ℚ)/m) p hnm2

  apply lt_of_lt_of_le hn at hnm
  exact Nat.ne_zero_of_lt hnm
  exact Nat.ne_zero_of_lt hn


lemma one_of_ipow_one (T : ContinuousTnorm) (n : ℕ) {p : I} : T.ipow n p = 1 → p = 1 := by
  by_cases hn : n = 0
  rw [hn, T.ipow_nat_zero]
  intro h;
  let h2 := zero_ne_one' ↑I
  contradiction

  intro h
  apply_fun (T.npow n) at h
  rw [pow_inv T n p hn, T.npow_I_one] at h
  exact h


-- This requires that T be strictly monotone
/-theorem inv_pow (T : ContinuousTnorm) (n : ℕ) (p : I) (h : n ≠ 0) : T.ipow n (T.npow n p) = p := by
  sorry
  --rw [← pow_inv_eq_inv_pow n n p]
  --exact pow_inv T n p h
-/


end Tnorm


-- Continuity of T.ipow requires that T be strictly monotone
/-theorem ipow_cont (T : ContinuousTnorm) (n : ℕ) : Continuous (T.ipow n) := by
  apply continuous_iff_seqContinuous.mpr
  intro x p hx
  apply Metric.tendsto_atTop.mpr; simp only [Function.comp_apply]
  intro ε he
  by_cases hn : n = 0
  rw [hn]; simp only [ge_iff_le, Tnorm.ipow_nat_zero, dist_self]
  use 1; intro n hnn; exact he

  let ε' := 1
  apply Metric.tendsto_atTop.mp at hx
  specialize hx ε' ?_--he;
  simp [ε', zero_lt_one]
  obtain ⟨N₁, hx⟩ := hx


  let hc := npow_uni_cont T n
  apply Metric.uniformContinuous_iff.mp at hc
  specialize hc ε he
  obtain ⟨δ, hd, hc⟩ := hc

  use N₁; intro m hm; specialize hx m hm
  by_cases hp : (x m) ≤ p
  by_cases hp0 : p = 0
  rw [hp0] at hp; apply le_zero_iff.mp at hp
  rw [hp0, hp, T.ipow_I_zero, dist_self]; exact he

  apply abs_sub_lt_iff.mp at hx
  apply And.right at hx
  let hi := T.ipow_le n hp

  apply abs_sub_lt_iff.mpr; constructor
  apply sub_left_lt_of_lt_add
  calc (T.ipow n (x m)).1
    _ ≤ T.ipow n p := hi
    _ < (T.ipow n p)+ε := lt_add_of_pos_right (↑(Tnorm.ipow n p)) he

  apply sub_left_lt_of_lt_add
  by_cases hepI : (T.ipow n (x m)) + ε > 1
  apply lt_of_le_of_lt (le_one (T.ipow n p)) hepI
  push_neg at hepI
  apply T.lt_of_npow_lt n (T.ipow n p) ⟨(T.ipow n (x m))+ε, by
    constructor
    exact add_nonneg (nonneg (T.ipow n (x m))) (le_of_lt he)
    exact hepI
    ⟩
  rw [Tnorm.pow_inv T]



  /-
  let δ' := (ε/2 ⊓ δ/2)
  have hd' : δ' > 0 := lt_min (half_pos he) (half_pos hd)
  suffices T.ipow n p ≤ T.ipow n (x m) + δ' by
    calc (T.ipow n p).1
      _ ≤ T.ipow n (x m) + δ' := this
      _ ≤ T.ipow n (x m) + (ε/2) := by refine add_le_add ?_ (min_le_left (ε / 2) (δ / 2)); rfl
      _ < T.ipow n (x m) + ε := (Real.add_lt_add_iff_left ↑(Tnorm.ipow n (x m))).mpr (div_two_lt_of_pos he)
  unfold Tnorm.ipow
  apply csSup_le
  use 0; simp only [Set.mem_image, Set.mem_setOf_eq, Set.Icc.coe_eq_zero, exists_eq_right]
  rw [T.npow_ne_zero_zero n hn]; exact unitInterval.pos_iff_ne_zero.mpr hp0

  intro b hb; simp at hb; obtain ⟨hbI, hb⟩ := hb
  refine tsub_le_iff_right.mp ?_
  by_cases hbe : δ' > b
  calc b-δ'
    _ ≤ 0 := by simp only [tsub_le_iff_right, zero_add]; exact le_of_lt hbe
    _ ≤ T.ipow n (x m) := nonneg (T.ipow n (x m))

  have hbeI : b-δ' ∈ I := by
    constructor;
    push_neg at hbe; exact sub_nonneg_of_le hbe
    refine tsub_le_iff_right.mpr ?_
    apply le_trans hbI.2 ((le_add_iff_nonneg_right 1).mpr (le_of_lt hd'))
  apply Subtype.mk_le_mk.mpr
  apply le_csSup

  apply bddAbove_def.mpr;
  use 1; intro y hy; simp at hy;
  obtain ⟨hyI, hy⟩ := hy; exact hyI.2

  simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, Set.mem_Icc, exists_and_right,
    exists_eq_right]
  use hbeI

  have hbbd : dist (⟨b, hbI⟩ : I) ⟨(b-δ'), hbeI⟩ < δ := by sorry
  specialize hc hbbd
  calc (T.npow n ⟨b-δ', hbeI⟩).1
    _ < (T.npow n ⟨b, hbI⟩) - ε := by sorry
    _ < p-ε := by sorry
    _ < (x m) := by sorry

  sorry

  exact hbeI-/


  sorry
-/
