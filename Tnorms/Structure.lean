import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Examples
import Tnorms.Algebra
import Tnorms.LeftContinuity
import Tnorms.Continuity
import Tnorms.LeftContinuousArchimedean

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Basic

open unitInterval


theorem npow_cont (T : ContinuousTnorm) (n : ℕ) : Continuous (fun (p : I) => T.npow n p) := by
  apply continuous_iff_seqContinuous.mpr
  intro x p hx
  induction' n with n ih
  apply tendsto_const_nhds

  simp at ih
  let y : ℕ → I := (fun m => T.npow n (x m))
  let h := T.cont x y p (T.npow n p) hx ih
  exact h

section namespace Tnorm

variable {T : Tnorm}

noncomputable
def ipow (n : ℕ) (p : I) : I :=
  ⟨sSup (Subtype.val '' {q : I | T.npow n q < p}), sup_mem_I⟩

noncomputable
def rpow (r : ℚ) (p : I) := T.npow r.num.toNat (T.ipow r.den p)

@[simp] lemma ipow_nat_one (p : I) : T.ipow 1 p = p := by
  unfold ipow
  apply Subtype.mk_eq_mk.mpr
  by_cases hp : p = 0
  rw [hp]
  have hs : (Subtype.val '' {q : I | T.npow 1 q < 0}) = ∅ := by simp
  rw [hs]
  apply Real.sSup_empty

  push_neg at hp
  apply unitInterval.pos_iff_ne_zero.mpr at hp
  refine csSup_eq_of_is_forall_le_of_forall_le_imp_ge ?_ ?_ ?_
  use 0; simp; exact hp
  intro q hq; simp at hq
  obtain ⟨hqI, hq⟩ := hq
  exact le_of_lt hq

  intro r hr
  refine forall_lt_imp_le_iff_le_of_dense.mp ?_
  intro q hq
  by_cases hqI : 0 < q
  specialize hr q ?_
  simp
  use ?_
  exact hq
  constructor
  exact le_of_lt hqI
  calc q
    _ ≤ p := le_of_lt hq
    _ ≤ 1 := le_one p
  exact hr
  push_neg at hqI
  apply le_trans hqI
  specialize hr 0
  simp at hr
  exact hr hp


@[simp] lemma ipow_nat_zero (p : I) : T.ipow 0 p = 0 := by
  unfold ipow
  apply Subtype.mk_eq_mk.mpr
  have h : (Subtype.val '' {q : I | T.npow 0 q < p}) = ∅ := by
    refine Set.image_eq_empty.mpr ?_
    refine Set.eq_empty_of_forall_not_mem ?_
    simp
    exact le_one p
  rw [h]
  apply Real.sSup_empty
@[simp] lemma ipow_I_zero (n : ℕ) : T.ipow n 0 = 0 := by
  unfold ipow
  apply Subtype.mk_eq_mk.mpr
  have h : (Subtype.val '' {q : I | T.npow n q < 0}) = ∅ := by simp
  rw [h]
  apply Real.sSup_empty

lemma npow_ne_zero_zero (n : ℕ) (h : n ≠ 0) : T.npow n 0 = 0 := by
  induction' n with n ih
  simp; exact h rfl
  by_cases hn : n = 0
  rw [hn]; simp
  specialize ih hn
  rw [T.npow_succ, ih, T.mul_zero]

variable {T : ContinuousTnorm}

lemma npow_I_one (T : Tnorm) (n : ℕ) : T.npow n 1 = 1 := by
  induction' n with n ih
  exact T.npow_zero 1
  rw [T.npow_succ, T.one_mul, ih]

lemma lt_of_npow_lt (T : Tnorm) (n : ℕ) (p q : I) : T.npow n p < T.npow n q → p < q := by
  contrapose!
  exact T.npow_le n q p


theorem pow_inv (T : ContinuousTnorm) (n : ℕ) (p : I) (h : n ≠ 0) : T.npow n (T.ipow n p) = p := by
  unfold ipow
  by_cases hp : p = 0

  have hemp : (Subtype.val '' {q : I | T.npow n q < p}) = ∅ := by
    apply Set.image_eq_empty.mpr
    refine Set.subset_empty_iff.mp ?_
    intro q; simp;
    rw [hp]; exact (T.npow n q).2.1
  have hempz : ⟨sSup (Subtype.val '' {q : I | T.npow n q < p}), sup_mem_I⟩ = (0 : I) := by
    apply Subtype.mk_eq_mk.mpr
    rw [hemp]; exact Real.sSup_empty
  rw [hempz]
  rw [T.npow_ne_zero_zero n h, hp]

  have hbdd : BddBelow (Subtype.val '' {q | T.npow n q = p}) := by
    apply bddBelow_def.mpr
    use 0; intro y hy; simp at hy
    obtain ⟨hyI, hy⟩ := hy
    exact hyI.1
  let r : I := ⟨sInf (Subtype.val '' {q | T.npow n q = p}), inf_mem_I⟩
  have hrp : T.npow n r = p := by
    have hrp : r.1 ∈ (Subtype.val '' {q | T.npow n q = p}) := by
      unfold r
      refine IsClosed.csInf_mem ?_ ?_ hbdd
      exact IsClosed.trans (isClosed_eq (npow_cont T n) continuous_const) isClosed_Icc

      have her : ∃ q : I, T.npow n q = p := by
        let h2 := intermediate_value_univ 0 1 (npow_cont T n)
        rw [T.npow_ne_zero_zero n h, T.npow_I_one n] at h2
        exact h2 p.2
      obtain ⟨q, hq⟩ := her
      use q; simp; constructor; exact q.2; exact hq

    simp at hrp
    exact hrp.2

  have hrs : r = sSup (Subtype.val '' {q | T.npow n q < p}) := by
    refine Eq.symm (csSup_eq_of_is_forall_le_of_forall_le_imp_ge ?_ ?_ ?_)

    use 0; simp; rw [T.npow_ne_zero_zero n h]; exact unitInterval.pos_iff_ne_zero.mpr hp

    intro a ha; simp at ha
    obtain ⟨haI, ha⟩ := ha
    rw [← hrp] at ha
    apply lt_of_npow_lt at ha
    exact le_of_lt ha

    intro ub hub
    by_contra! hurb
    have hr' : ub < (r+ub)/2 := by
      calc ub
        _ = (ub/2) + (ub/2) := Eq.symm (add_halves ub)
        _ < (r/2) + (ub/2) := (add_lt_add_iff_right (ub / 2)).mpr (div_lt_div_of_pos_right hurb zero_lt_two)
        _ = (r+ub)/2 := Eq.symm (add_div (↑r) ub 2)
    have hrr : (r+ub)/2 < r := by
      calc (r+ub)/2
        _ = (r/2)+(ub/2) := add_div (↑r) ub 2
        _ < (r/2)+(r/2) := (add_lt_add_iff_left (↑r / 2)).mpr (div_lt_div_of_pos_right hurb zero_lt_two)
        _ = r := add_halves r.1
    let r' : I := ⟨(r+ub)/2, by
      constructor
      calc 0
        _ ≤ ub := by specialize hub 0; simp at hub; rw
          [T.npow_ne_zero_zero n h] at hub; apply
          unitInterval.pos_iff_ne_zero.mpr at hp; exact hub hp
        _ ≤ (r+ub)/2 := le_of_lt hr'
      calc (r+ub)/2
        _ ≤ r := le_of_lt hrr
        _ ≤ 1 := le_one r
      ⟩
    have hr'p : T.npow n r' < p := by
      by_contra! hpow
      apply antisymm' at hpow
      specialize hpow ?_
      rw [← hrp]
      apply T.npow_le n r' r (le_of_lt hrr)

      conv at hrr => rhs; unfold r
      simp only at hrr
      have hrin : r'.1 ∈ (Subtype.val '' {q | T.npow n q = p}) := by
        simp; constructor; exact r'.2; exact hpow
      apply csInf_le hbdd at hrin
      apply not_le_of_lt at hrr
      contradiction

    specialize hub r' ?_
    simp [hr'p]; exact r'.2
    apply not_le_of_lt at hr'
    contradiction

  have hrs' : r = ⟨sSup (Subtype.val '' {q | T.npow n q < p}), sup_mem_I⟩ := Subtype.mk_eq_mk.mpr hrs
  rw [← hrs', hrp]


theorem ipow_mul (n m : ℕ) (p : I) : T.ipow n (T.ipow m p) = T.ipow (n*m) p := by
  by_cases hp : p = 0
  rw [hp, ipow_I_zero, ipow_I_zero, ipow_I_zero]
  apply unitInterval.pos_iff_ne_zero.mpr at hp
  by_cases hm : m = 0
  rw [hm, ipow_nat_zero, ipow_I_zero, Nat.mul_zero, ipow_nat_zero]

  unfold ipow
  apply Subtype.mk_eq_mk.mpr
  have hbdd : BddAbove (Subtype.val '' {q | T.npow m q < p}) := by
    apply bddAbove_def.mpr
    use 1; intro y hy; simp at hy; exact hy.1.2
  have hnempty : (Subtype.val '' {q | T.npow m q < p}).Nonempty := by
    use 0; simp
    rw [npow_ne_zero_zero m hm]
    exact hp
  refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
  intro x hx; simp at hx
  obtain ⟨hxI, hpow⟩ := hx
  use x
  constructor; swap; rfl
  simp; use hxI
  apply Subtype.mk_lt_mk.mp at hpow
  apply (lt_csSup_iff hbdd hnempty).mp at hpow
  obtain ⟨q, hq, hpow⟩ := hpow
  simp at hq
  obtain ⟨hqI, hq⟩ := hq
  calc T.npow (n*m) ⟨x, hxI⟩
    _ = T.npow m (T.npow n ⟨x, hxI⟩) := by rw [T.npow_mul, Nat.mul_comm]
    _ ≤ T.npow m ⟨q, hqI⟩ := by apply T.npow_le; exact le_of_lt hpow
    _ < p := hq

  intro x hx; simp at hx
  obtain ⟨hxI, hx⟩ := hx
  use x; simp; use hxI
  have hr : ⟨sSup (Subtype.val '' {q | T.npow m q < p}), sup_mem_I⟩ = T.ipow m p := by rfl
  rw [hr]
  by_contra h
  push_neg at h
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

theorem rpow_add (r s : ℚ) (p : I) (hr : r.num ≥ 0) (hs : s.num ≥ 0) : T.rpow (r+s) p = T.mul (T.rpow r p) (T.rpow s p) := by
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

end Tnorm


/- Major theorem about the structure of Tnorms that require representation approaches
  (using pseudo-inverses or generators or something like that)
-/

theorem luk_iso_of_nilpt {T : Tnorm} : Nilpotent T → Tnorm.Isomorphic Tnorm.LukTnorm.toTnorm T := by
  sorry
