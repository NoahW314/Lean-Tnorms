import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Examples
import Tnorms.Order
import Tnorms.Algebra
import Tnorms.Isomorphism


import Mathlib.Topology.UnitInterval

open unitInterval
open Classical


variable {T : Tnorm}

-- Proposition 1.9 (i)
theorem diag_min (h: ∀ p : I, T.mul p p = p) : T = ⊤ := by
  rw [Tnorm.min_top]
  ext p q
  rw [Tnorm.min_tnorm_def]
  wlog hpq : p ≤ q
  push_neg at hpq
  specialize this h q p (le_of_lt hpq)
  rw [T.mul_comm, min_comm]; exact this

  rw [min_eq_left hpq]; apply Subtype.coe_inj.mpr
  apply antisymm (T.mul_le_left p q)
  nth_rw 1 [← h p]
  apply T.mul_le_mul_left; exact hpq


-- Proposition 1.9 (ii)
theorem diag_drastic (h : ∀ p : I, p ≠ 1 → T.mul p p = 0) : T = ⊥ := by
  rw [Tnorm.drastic_bot]
  ext p q; apply Subtype.coe_inj.mpr
  by_cases hpq : p = 1 ∨ q = 1
  simp only [Tnorm.DrasticTnorm, hpq, ↓reduceIte]
  by_cases hp : p = 1
  rw [hp, T.one_mul, min_eq_right]; exact q.2.2
  simp only [hp, false_or] at hpq
  rw [hpq, T.mul_one, min_eq_left]; exact p.2.2

  simp only [Tnorm.DrasticTnorm, hpq, ↓reduceIte]
  wlog hpql : p ≤ q
  push_neg at hpql; apply le_of_lt at hpql
  specialize this h q p ?_ hpql
  push_neg; symm; push_neg at hpq; exact hpq
  rw [T.mul_comm]; exact this

  push_neg at hpq
  apply Subtype.coe_inj.mp
  apply antisymm ?_ (T.mul p q).2.1
  calc T.mul p q
    _ ≤ T.mul q q := by apply T.mul_le_mul_right; exact hpql
    _ = 0 := by apply h q hpq.2


-- Proposition 2.3 (i)
theorem idpt_iff_min (a : I) : T.mul a a = a ↔ ∀ p : I, a ≤ p → T.mul a p = a ⊓ p := by
  constructor; intro h p hap
  rw [min_eq_left hap]
  apply antisymm (T.mul_le_left a p)
  nth_rw 1 [← h]
  apply T.mul_le_mul_left; exact hap

  intro h; specialize h a ?_; rfl
  rw [h, min_self]

-- Proposition 2.3 (ii)
theorem idpt_iff_min' (T : ContinuousTnorm) (a : I) : T.mul a a = a ↔ ∀ p : I, T.mul a p = a ⊓ p := by
  constructor; intro h p
  by_cases hap : a ≤ p
  exact (idpt_iff_min a).mp h p hap
  push_neg at hap
  let hc := T.cont
  apply (cont_one_var T.toTnorm).mp at hc
  specialize hc a
  apply intermediate_value_univ 0 a at hc
  rw [T.mul_zero, h] at hc
  have hp : p ∈ Set.Icc 0 a := by
    constructor; exact nonneg p
    exact le_of_lt hap
  apply hc at hp
  simp only [Set.mem_range, Subtype.exists] at hp
  obtain ⟨q', hqI, hpq⟩ := hp
  nth_rw 1 [← hpq, ← T.mul_assoc, h, hpq, min_eq_right (le_of_lt hap)]

  intro h; specialize h a
  rw [h, min_self]

-- Remark 2.4 (iv)
theorem le_nilpt (p q : I) : q ≤ p → (∃ n : ℕ, T.npow n p = 0) → (∃ m : ℕ, T.npow m q = 0) := by
  intro hpq hp
  obtain ⟨n, hp⟩ := hp
  use n
  apply le_zero_iff.mp
  rw [← hp]
  apply T.npow_le
  exact hpq

-- Remark 2.4 (v)
def IsNilpotentI (T : Tnorm) (p : I) := IsNontrivial p ∧ ∃ n : ℕ, T.npow n p = 0
theorem nilpt_els_interval : ∃ c : I, ({p : I | IsNilpotentI T p} = Set.Ioo 0 c) ∨
  ({p : I | IsNilpotentI T p} = Set.Ioc 0 c) := by
  let c := sSup {p : I | IsNilpotentI T p}
  use c
  by_cases hc : ∃ n : ℕ, T.npow n c = 0
  right
  ext p; rw [Set.mem_Ioc]; constructor
  intro hp; constructor
  rw [Set.mem_setOf] at hp
  apply And.left at hp; apply And.left at hp
  apply unitInterval.pos_iff_ne_zero.mpr hp
  apply le_sSup hp

  intro hp; rw [Set.mem_setOf]; constructor; constructor
  apply unitInterval.pos_iff_ne_zero.mp hp.1
  apply unitInterval.lt_one_iff_ne_one.mp
  apply lt_of_le_of_lt hp.2; apply unitInterval.lt_one_iff_ne_one.mpr
  by_contra hc1
  obtain ⟨n, hn⟩ := hc
  rw [hc1, T.npow_I_one] at hn
  exact one_ne_zero hn
  apply le_nilpt c p hp.2 hc


  left
  ext p; rw [Set.mem_Ioo, Set.mem_setOf]; constructor
  intro hp;  constructor
  apply unitInterval.pos_iff_ne_zero.mpr hp.1.1
  contrapose! hc
  apply le_nilpt p c hc hp.2

  intro hp; constructor; constructor
  apply unitInterval.pos_iff_ne_zero.mp hp.1
  apply unitInterval.lt_one_iff_ne_one.mp
  apply lt_of_lt_of_le hp.2 (le_one c)
  apply And.right at hp
  apply lt_sSup_iff.mp at hp
  obtain ⟨q, hp, hpq⟩ := hp
  rw [Set.mem_setOf] at hp
  apply le_nilpt q p (le_of_lt hpq) hp.2

noncomputable def choose_subseq (A : Set ℕ) (hA : ∀ x : ℕ, ∃ y ∈ A, x < y) : ℕ → ℕ :=
  let rec n : ℕ → ℕ := fun k =>
    match k with
    | Nat.zero => Classical.choose (hA 0)
    | (Nat.succ j) => Classical.choose (hA (n j))
  n
lemma choose_subseq_is_subseq (A : Set ℕ) (hA : ∀ x : ℕ, ∃ y ∈ A, x < y) : StrictMono (choose_subseq A hA) := by
  intro i j hij
  induction j with
  | zero => contradiction
  | succ k ih =>
    suffices choose_subseq A hA k < choose_subseq A hA (k+1) by
      by_cases hk : i < k
      specialize ih hk
      apply lt_trans ih this

      push_neg at hk
      have hik := Nat.eq_of_le_of_lt_succ hk hij
      rw [hik]; exact this
    exact (Classical.choose_spec (hA (choose_subseq A hA k))).2
lemma above_or_below (a : I) (x : ℕ → I) (h : Filter.Tendsto x Filter.atTop (nhds a)) :
  ¬BddAbove {k : ℕ | ∀ j : ℕ, j ≥ k → x k ≤ x j} ∨ ¬BddAbove {k : ℕ | ∀ j : ℕ, j ≥ k → x k ≥ x j} := by
    rw [← not_and_or, not_and]
    intro hb
    have hnbad : (∀ z : ℕ, ∃ y ∈ {k : ℕ | ∀ j : ℕ, j ≥ k → x k ≥ x j}, z ≤ y) → ¬BddAbove {k : ℕ | ∀ j : ℕ, j ≥ k → x k ≥ x j} := by
      intro h; exact not_bddAbove_iff.mpr fun x ↦ h x.succ

    apply hnbad
    intro m;
    apply bddAbove_def.mp at hb
    obtain ⟨m', hb⟩ := hb

    by_cases hb2 : BddAbove {n : ℕ | x n ≠ a}
    apply bddAbove_def.mp at hb2
    obtain ⟨N, hb2⟩ := hb2
    use (m ⊔ (N+1)); constructor; swap; exact le_max_left m (N+1)
    rw [Set.mem_setOf]; intro j hj
    suffices ∀ l > N, x l = a by
      let hN := lt_of_lt_of_le (lt_add_one N) (le_max_right m (N+1))
      rw [this (max m (N+1)) hN, this j]
      apply lt_of_lt_of_le hN hj
    intro l hl
    specialize hb2 l; rw [Set.mem_setOf] at hb2
    contrapose! hb2; constructor; exact hb2; exact hl


    apply bddAbove_def.not.mp at hb2; push_neg at hb2
    obtain ⟨n, hn⟩ := hb2 (m ⊔ m'); rw [Set.mem_setOf] at hn
    let C := {N : ℕ | n ≤ N ∧ ∀ k > N, dist (x k) a < dist (x n) a}
    let k := sInf C
    have hkC : k ∈ C := by
      apply Nat.sInf_mem
      apply Metric.tendsto_atTop.mp at h
      specialize h (dist (x n) a) (dist_pos.mpr hn.1)
      obtain ⟨N, h⟩ := h
      use N ⊔ n; unfold C; rw [Set.mem_setOf]; constructor
      exact le_max_right N n
      intro k hk
      apply le_of_lt at hk
      apply le_trans (le_max_left N n) at hk
      exact h k hk
    use k; constructor; rw [Set.mem_setOf]
    intro j hjk

    rw [Set.mem_setOf] at hkC
    rcases Nat.lt_or_eq_of_le hjk with hjk|hjk
    let hk := hkC.2
    specialize hk j hjk
    have hxk : dist (x k) a ≥ dist (x n) a := by
      by_cases hnk : k = n; rw [hnk]

      apply lt_of_le_of_ne' hkC.1 at hnk
      by_contra!
      suffices k ≠ sInf C by contradiction
      apply ne_of_gt; apply lt_of_le_of_lt ?_ (Nat.sub_one_lt_of_lt hnk)
      apply Nat.sInf_le
      unfold C; rw [Set.mem_setOf]; constructor
      exact Nat.le_sub_one_of_lt hnk
      intro j hjk
      by_cases hjk' : j = k
      rw [hjk']; exact this
      exact hkC.2 j (lt_of_le_of_ne' (Nat.le_of_pred_lt hjk) hjk')
    by_cases hxka : (x k) ≤ a
    suffices ∀ i ≥ k, x k ≤ x i by
      specialize hb k; rw [Set.mem_setOf] at hb; specialize hb this
      apply le_trans hkC.1 at hb
      apply lt_of_lt_of_le hn.2 at hb
      apply lt_of_le_of_lt (le_max_right m m') at hb
      apply (lt_self_iff_false m').mp at hb
      contradiction
    intro i hik
    rcases Nat.eq_or_lt_of_le hik with hik|hik
    rw [hik]
    let hk := hkC.2
    specialize hk i hik
    calc (x k).1
      _ ≤ a-(dist (x n) a) := by
        suffices dist (x k) a = -((x k).1-a) by
          rw [this] at hxk
          apply le_sub_comm.mp
          apply le_trans hxk
          ring_nf; rfl
        apply abs_eq_neg_self.mpr
        exact tsub_nonpos.mpr hxka
      _ ≤ a-|(x i).1-a| := by exact sub_le_sub_left (le_of_lt hk) a.1
      _ ≤ a-(-((x i).1-a)) := by apply sub_le_sub_left ?_ a.1; apply neg_le_abs
      _ = x i := by ring



    push_neg at hxka; apply le_of_lt at hxka
    calc (x k).1
      _ ≥ a+(dist (x n) a) := by
        suffices dist (x k) a = (x k).1-a by
          rw [this] at hxk
          exact le_sub_iff_add_le'.mp hxk
        apply abs_eq_self.mpr
        exact sub_nonneg_of_le hxka
      _ ≥ a+|(x j).1-a| := by exact add_le_add_left (le_of_lt hk) a.1
      _ ≥ a+((x j).1-a) := by apply add_le_add_left ?_ a.1; apply le_abs_self
      _ = (x j) := by ring

    rw [hjk]

    rw [Set.mem_setOf] at hkC
    apply le_trans (le_max_left m m')
    apply le_trans (le_of_lt hn.2) hkC.1

lemma mono_or_anti_of_tendsto (a : I) (x : ℕ → I) (h : Filter.Tendsto x Filter.atTop (nhds a)) :
  ∃ n : ℕ → ℕ, StrictMono n  ∧ ((Monotone (x ∘ n)) ∨ (Antitone (x ∘ n))) := by
    let A := {k : ℕ | ∀ j : ℕ, j ≥ k → x k ≤ x j}
    let B := { k : ℕ | ∀ j : ℕ, j ≥ k → x k ≥ x j}
    rcases above_or_below a x h with hA|hB

    apply bddAbove_def.not.mp at hA; push_neg at hA
    use choose_subseq A hA; constructor; exact choose_subseq_is_subseq A hA; left
    intro k k' hkk; rw [Function.comp_apply, Function.comp_apply]
    apply StrictMono.monotone (choose_subseq_is_subseq A hA) at hkk
    match k with
    | 0 =>
      have hcA := (Classical.choose_spec (hA 0)).1
      unfold A at hcA; rw [Set.mem_setOf] at hcA
      exact hcA (choose_subseq A hA k') hkk
    | j+1 =>
      have hcA := (Classical.choose_spec (hA (choose_subseq A hA j))).1
      unfold A at hcA; rw [Set.mem_setOf] at hcA
      exact hcA (choose_subseq A hA k') hkk

    apply bddAbove_def.not.mp at hB; push_neg at hB
    use choose_subseq B hB; constructor; exact choose_subseq_is_subseq B hB; right
    intro k k' hkk; rw [Function.comp_apply, Function.comp_apply]
    apply StrictMono.monotone (choose_subseq_is_subseq B hB) at hkk
    match k with
    | 0 =>
      have hcB := (Classical.choose_spec (hB 0)).1
      unfold B at hcB; rw [Set.mem_setOf] at hcB
      exact hcB (choose_subseq B hB k') hkk
    | j+1 =>
      have hcB := (Classical.choose_spec (hB (choose_subseq B hB j))).1
      unfold B at hcB; rw [Set.mem_setOf] at hcB
      exact hcB (choose_subseq B hB k') hkk


-- Corollary 2.8
theorem idpts_closed (h : ∀ a : I, ∀ x : ℕ → I, (Antitone x →
  Filter.Tendsto (fun n => T.mul (x n) (x n)) Filter.atTop (nhds a) → T.mul a a = a)) :
  IsClosed {a : I | T.mul a a = a} := by
    apply closure_subset_iff_isClosed.mp
    intro a ha; rw [Set.mem_setOf]
    apply Metric.mem_closure_iff.mp at ha
    let x : ℕ → I := fun n => Classical.choose (ha (1/(n+1)) (by exact Nat.one_div_pos_of_nat))
    have hxid : ∀ n : ℕ, T.mul (x n) (x n) = (x n) := by
      intro n
      have h := (Classical.choose_spec (ha (1/(n+1)) (by exact Nat.one_div_pos_of_nat))).1
      rw [Set.mem_setOf] at h
      exact h
    have hx : Filter.Tendsto x Filter.atTop (nhds a) := by
      apply Metric.tendsto_atTop.mpr
      intro ε he
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt he
      use N; intro n hn
      have hxn := (Classical.choose_spec (ha (1/(n+1)) (by exact Nat.one_div_pos_of_nat))).2
      calc dist (x n) a
        _ = dist a (x n) := by rw [dist_comm]
        _ < 1/(n+1) := hxn
        _ ≤ 1/(N+1) := by
          apply div_le_div₀ (zero_le_one) (by rfl) (Nat.cast_add_one_pos N)
          exact_mod_cast add_le_add_right hn 1
        _ < ε := hN
    obtain ⟨n, hn, hmax⟩ := mono_or_anti_of_tendsto a x hx
    rcases hmax with hmx|hax

    apply antisymm (T.mul_le_left a a)
    let hx' := Filter.Tendsto.comp hx (StrictMono.tendsto_atTop hn)
    let hlub := isLUB_of_tendsto_atTop hmx hx'
    apply (isLUB_le_iff hlub).mpr
    rw [mem_upperBounds]
    intro y hy; rw [Set.mem_range] at hy
    obtain ⟨k, hy⟩ := hy; rw [← hy]
    rw [Function.comp_apply, ← hxid (n k)]
    suffices x (n k) ≤ a by apply T.mul_le_mul; exact this; exact this
    apply Monotone.ge_of_tendsto hmx hx'



    apply h a (x ∘ n) hax
    suffices ∀ k : ℕ, T.mul ((x ∘ n) k) ((x ∘ n) k) = x (n k) by
      simp only [this]
      suffices Filter.Tendsto (x ∘ n) Filter.atTop (nhds a) by exact this
      apply Filter.Tendsto.comp hx
      exact StrictMono.tendsto_atTop hn
    intro k; rw [Function.comp_apply]
    exact hxid (n k)



def Isomorphisms : Set (I → I) := {φ : I → I | Tnorm.Isomorphism φ}
-- Proposition 2.31
theorem iso_invariants {T : Tnorm} : (∀ φ : Isomorphisms, Tnorm.apply_iso T φ.2 = T)
  ↔ T = Tnorm.MinTnorm.toTnorm ∨ T = Tnorm.DrasticTnorm := by
  constructor; swap; intro h
  intro ⟨φ, hφ⟩; rw [Isomorphisms, Set.mem_setOf] at hφ
  ext p q
  rcases h with h|h

  simp [Tnorm.apply_iso, h, Tnorm.min_tnorm_def]
  by_cases hpq : p ≤ q
  let hpq' := hφ.2 hpq
  rw [min_eq_left hpq, min_eq_left hpq', Function.leftInverse_invFun hφ.1.1]
  push_neg at hpq; apply le_of_lt at hpq
  let hpq' := hφ.2 hpq
  rw [min_eq_right hpq, min_eq_right hpq', Function.leftInverse_invFun hφ.1.1]

  simp only [Tnorm.apply_iso, h, Tnorm.drastic_def]
  by_cases hpq : p = 1 ∨ q = 1
  rcases hpq with hp | hq

  simp only [hp, Tnorm.iso_one hφ, true_or, reduceIte]
  rw [min_eq_right, min_eq_right, Function.leftInverse_invFun hφ.1.1]
  exact le_one q; exact le_one (φ q)

  simp only [hq, Tnorm.iso_one hφ, or_true, reduceIte]
  rw [min_eq_left, min_eq_left, Function.leftInverse_invFun hφ.1.1]
  exact le_one p; exact le_one (φ p)

  have hpq' : ¬(φ p = 1 ∨ φ q = 1) := by
    contrapose! hpq
    rcases hpq with hp | hq
    left; rw [← Tnorm.iso_one hφ] at hp
    apply hφ.1.1 hp

    right; rw [← Tnorm.iso_one hφ] at hq
    apply hφ.1.1 hq
  simp only [hpq, hpq', reduceIte]
  rw [Tnorm.iso_zero (Tnorm.iso_inv_is_iso hφ)]



  intro h
  by_cases hid : ∀ p : I, T.mul p p = p
  left; exact diag_min hid

  right; apply diag_drastic
  push_neg at hid
  obtain ⟨p₀, hid⟩ := hid
  apply lt_of_le_of_ne (T.mul_self_le_self p₀) at hid
  intro p hp
  by_cases hpp : p = 0
  rw [hpp, T.mul_zero]
  have hpnt : IsNontrivial p := by constructor; exact hpp; exact hp
  have hp₀0 : p₀.1 ≠ 0 := by
    contrapose! hid
    apply Set.Icc.coe_eq_zero.mp at hid
    rw [hid, T.mul_zero]
  have hp₀1 : p₀ ≠ 1 := by
    contrapose! hid
    rw [hid, T.mul_one]

  have hqdiv : ∀ q : I, q > p₀ → p+(1-p.1)/(1-p₀)*(q-p₀) ∈ I := by
    intro q hpq; constructor
    apply add_nonneg p.2.1
    apply mul_nonneg
    apply div_nonneg; unit_interval; unit_interval
    simp only [sub_nonneg, Subtype.coe_le_coe]
    exact le_of_lt hpq

    rw [div_mul_comm]
    suffices (q.1-p₀)/(1-p₀) ≤ 1 by
      calc p.1+((q.1-p₀)/(1-p₀))*(1-p)
        _ ≤ p+(1-p) := by
          apply add_le_add_left
          apply mul_le_of_le_one_left ?_ this
          unit_interval
        _ = 1 := by ring
    apply (div_le_one ?_).mpr
    apply sub_le_sub_right q.2.2
    rw [sub_pos]
    apply unitInterval.lt_one_iff_ne_one.mpr hp₀1
  let φ : I → I := fun q => ⟨if q ≤ p₀ then p/p₀*q else p+(1-p)/(1-p₀)*(q-p₀), by
    by_cases hpq : q ≤ p₀
    simp only [hpq, reduceIte]; constructor
    apply mul_nonneg (div_nonneg p.2.1 p₀.2.1) q.2.1
    rw [div_mul_comm]
    apply mul_le_one₀ ?_ p.2.1 p.2.2
    refine (div_le_one₀ ?_).mpr hpq
    exact unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)

    simp only [hpq, reduceIte]; push_neg at hpq
    exact hqdiv q hpq
    ⟩
  let ψ : I → I := fun q => ⟨if q ≤ p₀ then p/√p₀*√q else p+(1-p)/(1-p₀)*(q-p₀), by
    by_cases hpq : q ≤ p₀
    simp only [hpq, reduceIte]; constructor
    apply mul_nonneg (div_nonneg p.2.1 (Real.sqrt_nonneg p₀.1)) (Real.sqrt_nonneg q.1)
    rw [div_mul_comm, ← Real.sqrt_div q.2.1]
    apply mul_le_one₀ ?_ p.2.1 p.2.2
    apply Real.sqrt_le_one.mpr
    refine (div_le_one₀ ?_).mpr hpq
    exact unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)

    simp only [hpq, reduceIte]; push_neg at hpq
    exact hqdiv q hpq
    ⟩

  have hrtop : ∀ r : I, r > p → ∃ q : I, r.1 = p+(1-p)/(1-p₀)*(q-p₀) ∧ ¬q ≤ p₀ := by
    intro r hrp
    have hqI : (1-p₀.1)/(1-p)*(r-p)+p₀ ∈ I := by
      constructor
      apply add_nonneg ?_ p₀.2.1
      apply mul_nonneg; apply div_nonneg
      unit_interval; unit_interval; rw [sub_nonneg]; exact le_of_lt hrp

      rw [div_mul_comm]
      calc (r.1-p)/(1-p)*(1-p₀)+p₀
        _ ≤ 1*(1-p₀)+p₀ := by
          apply add_le_add_right
          apply (mul_le_mul_right ?_).mpr
          apply (div_le_one ?_).mpr
          apply sub_le_sub_right; exact r.2.2
          rw [sub_pos]; apply unitInterval.lt_one_iff_ne_one.mpr hp
          rw [sub_pos]; apply unitInterval.lt_one_iff_ne_one.mpr hp₀1
        _ = 1 := by ring
    use ⟨(1-p₀)/(1-p)*(r-p)+p₀, hqI⟩; constructor
    rw [add_sub_cancel_right, ← mul_assoc, div_mul_div_cancel₀, div_self, one_mul, add_sub_cancel]
    rw [sub_ne_zero]; symm; apply coe_ne_one.mpr hp
    rw [sub_ne_zero]; symm; apply coe_ne_one.mpr hp₀1

    push_neg; apply Subtype.mk_lt_mk.mpr
    refine lt_add_of_pos_of_le ?_ ?_; swap; rfl
    apply mul_pos; apply div_pos
    rw [sub_pos]; apply unitInterval.lt_one_iff_ne_one.mpr hp₀1
    rw [sub_pos]; apply unitInterval.lt_one_iff_ne_one.mpr hp
    rw [sub_pos]; exact hrp

  have hpdiv : 0 < (1-p.1)/(1-p₀) := by
      apply div_pos
      rw [sub_pos]; apply unitInterval.lt_one_iff_ne_one.mpr hp
      rw [sub_pos]; apply unitInterval.lt_one_iff_ne_one.mpr hp₀1

  have hrsm : ∀ q r : I, q < r → q > p₀ → (p.1+(1-p)/(1-p₀)*(q-p₀)) < (p+(1-p)/(1-p₀)*(r-p₀)) := by
    intro q r hqr hqp
    apply add_lt_add_left
    apply (mul_lt_mul_left ?_).mpr
    apply sub_lt_sub_right
    apply Subtype.coe_lt_coe.mpr hqr
    exact hpdiv

  have hφ : Tnorm.Isomorphism φ := by
    suffices StrictMono φ ∧ Function.Surjective φ by
      constructor; constructor
      exact StrictMono.injective this.1
      exact this.2
      exact StrictMono.monotone this.1
    constructor
    intro q r hqr; unfold φ
    by_cases hrp : r ≤ p₀
    have hqp : q ≤ p₀ := le_trans (le_of_lt hqr) hrp
    simp only [hrp, hqp, reduceIte, Subtype.mk_lt_mk]
    apply (mul_lt_mul_left ?_).mpr
    apply Subtype.coe_lt_coe.mpr hqr
    apply div_pos
    apply unitInterval.pos_iff_ne_zero.mpr hpp
    apply unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)

    by_cases hqp : ¬q ≤ p₀
    simp only [hrp, hqp, reduceIte, Subtype.mk_lt_mk]; push_neg at hqp
    exact hrsm q r hqr hqp

    push_neg at hqp
    simp only [hrp, hqp, reduceIte, Subtype.mk_lt_mk]; push_neg at hrp
    calc p.1/p₀*q
      _ ≤ p := by
        rw [div_mul_comm]; nth_rw 2 [← one_mul p.1]
        apply (mul_le_mul_right ?_).mpr
        apply (div_le_one ?_).mpr; exact hqp
        apply unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)
        apply unitInterval.pos_iff_ne_zero.mpr hpp
      _ < p+(1-p)/(1-p₀)*(r-p₀) := by
        apply lt_add_of_le_of_pos ?_ ?_; rfl
        apply mul_pos; exact hpdiv
        rw [sub_pos, Subtype.coe_lt_coe]; exact hrp


    intro r
    by_cases hpr : r ≤ p
    have hpprI : p₀.1/p*r ∈ I := by
      rw [div_mul_comm]
      apply mul_mem ?_ p₀.2
      apply unitInterval.div_mem r.2.1 p.2.1 hpr
    use ⟨p₀.1/p*r, hpprI⟩
    have hppr : ⟨p₀.1/p*r, hpprI⟩ ≤ p₀ := by
      apply Subtype.mk_le_mk.mpr
      rw [div_mul_comm]; nth_rw 2 [← one_mul p₀.1]
      apply (mul_le_mul_right ?_).mpr
      apply (div_le_one ?_).mpr; exact hpr
      apply unitInterval.pos_iff_ne_zero.mpr hpp
      apply unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)
    simp only [φ, hppr, reduceIte]; apply Subtype.mk_eq_mk.mpr
    rw [← mul_assoc, div_mul_div_cancel₀, div_self, one_mul]
    apply coe_ne_zero.mpr hpp; exact hp₀0

    push_neg at hpr
    apply hrtop r at hpr
    obtain ⟨q, hpr, hqp⟩ := hpr
    use q
    simp only [φ, hqp, reduceIte]; rw [Subtype.mk_eq_mk.mpr]
    symm; exact hpr

  have hψ : Tnorm.Isomorphism ψ := by
    suffices StrictMono ψ ∧ Function.Surjective ψ by
      constructor; constructor
      exact StrictMono.injective this.1
      exact this.2
      exact StrictMono.monotone this.1
    constructor
    intro q r hqr; unfold ψ
    by_cases hrp : r ≤ p₀
    have hqp : q ≤ p₀ := le_trans (le_of_lt hqr) hrp
    simp only [hrp, hqp, reduceIte, Subtype.mk_lt_mk]
    apply (mul_lt_mul_left ?_).mpr
    apply Real.sqrt_lt_sqrt q.2.1 hqr
    apply div_pos
    apply unitInterval.pos_iff_ne_zero.mpr hpp
    apply Real.sqrt_pos.mpr; apply unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)

    by_cases hqp : ¬q ≤ p₀
    simp only [hrp, hqp, reduceIte, Subtype.mk_lt_mk]; push_neg at hqp
    exact hrsm q r hqr hqp

    push_neg at hqp
    simp only [hrp, hqp, reduceIte, Subtype.mk_lt_mk]; push_neg at hrp
    calc p.1/√p₀*√q
      _ ≤ p := by
        rw [div_mul_comm, ← Real.sqrt_div q.2.1]; nth_rw 2 [← one_mul p.1]
        apply (mul_le_mul_right ?_).mpr
        apply Real.sqrt_le_one.mpr
        apply (div_le_one ?_).mpr; exact hqp
        apply unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)
        apply unitInterval.pos_iff_ne_zero.mpr hpp
      _ < p+(1-p)/(1-p₀)*(r-p₀) := by
        apply lt_add_of_le_of_pos ?_ ?_; rfl
        apply mul_pos; exact hpdiv
        rw [sub_pos, Subtype.coe_lt_coe]; exact hrp



    intro r
    by_cases hpr : r ≤ p
    have hpprI : (√p₀.1/p*r)^2 ∈ I := by
      rw [div_mul_comm, pow_two]
      suffices (r.1/p*√p₀)∈ I by exact mul_mem this this
      apply unitInterval.mul_mem
      apply div_mem r.2.1 p.2.1 hpr
      constructor
      apply Real.sqrt_nonneg
      apply Real.sqrt_le_one.mpr p₀.2.2
    use ⟨(√p₀.1/p*r)^2, hpprI⟩
    have hppr : ⟨(√p₀.1/p*r)^2, hpprI⟩ ≤ p₀ := by
      apply Subtype.mk_le_mk.mpr
      rw [div_mul_comm, mul_pow, Real.sq_sqrt]; nth_rw 2 [← one_mul p₀.1]
      apply (mul_le_mul_right ?_).mpr
      apply (sq_le_one_iff₀ ?_).mpr
      apply (div_le_one ?_).mpr; exact hpr
      apply unitInterval.pos_iff_ne_zero.mpr hpp
      apply div_nonneg r.2.1 p.2.1
      apply unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)
      exact p₀.2.1
    simp only [ψ, hppr, reduceIte]; apply Subtype.mk_eq_mk.mpr
    rw [Real.sqrt_sq, ← mul_assoc, div_mul_div_cancel₀, div_self, one_mul]
    exact coe_ne_zero.mpr hpp; apply (Real.sqrt_ne_zero p₀.2.1).mpr hp₀0
    apply mul_nonneg; apply div_nonneg; apply Real.sqrt_nonneg
    exact p.2.1; exact r.2.1


    push_neg at hpr
    apply hrtop r at hpr
    obtain ⟨q, hpr, hqp⟩ := hpr
    use q
    simp only [ψ, hqp, reduceIte]; rw [Subtype.mk_eq_mk.mpr]
    symm; exact hpr

  have hmfp : (T.mul p p).1/p ≤ 1 := by
    apply (div_le_one₀ ?_).mpr
    apply T.mul_self_le_self p
    apply unitInterval.pos_iff_ne_zero.mpr hpp
  let hφ' := h ⟨φ, hφ⟩; let hψ' := h ⟨ψ, hψ⟩
  have hφp : p₀.1/p*(T.mul p p) = T.mul p₀ p₀ := by
    have hpI : p₀.1/p*(T.mul p p) ∈ I := by
      rw [div_mul_comm]
      apply unitInterval.mul_mem ?_ p₀.2
      apply unitInterval.div_mem (T.mul p p).2.1 p.2.1
      apply Subtype.coe_le_coe.mpr (T.mul_self_le_self p)
    suffices ⟨p₀.1/p*(T.mul p p), hpI⟩ = T.mul p₀ p₀ by apply Subtype.mk_eq_mk.mp this

    nth_rw 2 [← hφ']
    simp only [Tnorm.apply_iso, φ, le_refl, reduceIte]
    apply_fun φ; swap; exact hφ.1.1
    rw [Function.rightInverse_invFun hφ.1.2]
    have hpl : ⟨p₀.1/p*(T.mul p p), hpI⟩ ≤ p₀ := by
      apply Subtype.mk_le_mk.mpr
      rw [div_mul_comm]; nth_rw 2 [← one_mul p₀.1]
      apply (mul_le_mul_right ?_).mpr
      exact hmfp
      apply unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)
    simp only [φ, hpl, reduceIte]
    apply Subtype.mk_eq_mk.mpr
    have hpdiv : p.1/p₀*p₀ = p := by exact div_mul_cancel₀ (↑p) hp₀0
    have hppI : p.1/p₀*p₀ ∈ I := by rw [hpdiv]; exact p.2
    calc (p.1/p₀)*(p₀/p*(T.mul p p))
      _ = (p*(p.1)⁻¹)*(p₀*(p₀.1)⁻¹)*(T.mul p p) := by ring
      _ = T.mul p p := by
        rw [mul_inv_cancel₀ hp₀0, mul_inv_cancel₀ (coe_ne_zero.mpr hpp)]
        ring
      _ = T.mul ⟨p.1/p₀*p₀, hppI⟩ ⟨p.1/p₀*p₀, hppI⟩ := by
        have hpI' : ⟨p.1/p₀*p₀, hppI⟩ = p := by apply Subtype.mk_eq_mk.mpr hpdiv
        rw [hpI']
  have hψp : p₀.1/(p^2)*(T.mul p p)^2 = T.mul p₀ p₀ := by
    have hpI : p₀.1/(p^2)*(T.mul p p)^2 ∈ I := by
      rw [div_mul_comm, ← div_pow, pow_two]
      apply unitInterval.mul_mem ?_ p₀.2
      suffices (T.mul p p).1/p ∈ I by apply unitInterval.mul_mem this this
      apply unitInterval.div_mem (T.mul p p).2.1 p.2.1
      apply Subtype.coe_le_coe.mpr (T.mul_self_le_self p)
    suffices ⟨p₀.1/(p^2)*(T.mul p p)^2, hpI⟩ = T.mul p₀ p₀ by apply Subtype.mk_eq_mk.mp this

    nth_rw 2 [← hψ']
    simp only [Tnorm.apply_iso, ψ, le_rfl, reduceIte]
    apply_fun ψ; swap; exact hψ.1.1
    rw [Function.rightInverse_invFun hψ.1.2]
    have hpl : ⟨p₀.1/p^2*(T.mul p p)^2, hpI⟩ ≤ p₀ := by
      apply Subtype.mk_le_mk.mpr
      rw [div_mul_comm]; nth_rw 2 [← one_mul p₀.1]
      apply (mul_le_mul_right ?_).mpr
      rw [← div_pow]; apply (sq_le_one_iff₀ ?_).mpr hmfp
      apply div_nonneg (T.mul p p).2.1 p.2.1
      apply unitInterval.pos_iff_ne_zero.mpr (coe_ne_zero.mp hp₀0)
    simp only [ψ, hpl, reduceIte]
    apply Subtype.mk_eq_mk.mpr
    have hpdiv : p.1/√p₀*√p₀ = p := by
      apply div_mul_cancel₀
      exact (Real.sqrt_ne_zero (nonneg p₀)).mpr hp₀0
    have hppI : p.1/√p₀*√p₀ ∈ I := by rw [hpdiv]; exact p.2
    calc p.1/√p₀*√(p₀/p^2*(T.mul p p)^2)
      _ = p.1/√p₀*(√p₀/√(p^2)*√((T.mul p p)^2)) := by
        rw [Real.sqrt_mul, Real.sqrt_div (nonneg p₀)]
        apply div_nonneg (nonneg p₀) ?_
        apply sq_nonneg p.1
      _ = p.1/√p₀*(√p₀/p*(T.mul p p)) := by
        rw [Real.sqrt_sq p.2.1, Real.sqrt_sq]
        unit_interval
      _ = (√p₀*(√p₀)⁻¹)*(p*(p.1)⁻¹)*(T.mul p p) := by ring
      _ = T.mul p p := by
        rw [mul_inv_cancel₀, mul_inv_cancel₀, one_mul, one_mul]
        exact coe_ne_zero.mpr hpp
        exact (Real.sqrt_ne_zero (nonneg p₀)).mpr hp₀0
      _ = T.mul ⟨p.1/√p₀*√p₀, hppI⟩ ⟨p.1/√p₀*√p₀, hppI⟩ := by
        have hpI' : ⟨p.1/√p₀*√p₀, hppI⟩ = p := by apply Subtype.mk_eq_mk.mpr hpdiv
        rw [hpI']

  rw [← hφp] at hψp
  ring_nf at hψp
  rw [pow_two, pow_two, mul_assoc p₀.1, mul_assoc p₀.1] at hψp
  apply mul_left_cancel₀ hp₀0 at hψp
  rw [mul_assoc] at hψp
  apply mul_left_cancel₀ (inv_ne_zero (coe_ne_zero.mpr hpp)) at hψp
  rw [← mul_assoc] at hψp; nth_rw 3 [← one_mul (T.mul p p).1] at hψp
  contrapose! hid
  apply le_of_eq; apply Subtype.coe_inj.mp
  rw [← hφp]; ring_nf; rw [mul_assoc]; nth_rw 1 [← mul_one p₀.1]
  congr; apply coe_ne_zero.mpr at hid
  apply mul_right_cancel₀ hid at hψp
  symm; exact hψp
