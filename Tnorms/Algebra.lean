import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Continuity

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Metrizable.CompletelyMetrizable

open unitInterval

/-
The goal of this file is to define some properties that T-norms might possess and prove
  relationships between these properties.  See (Triangular Norms I, Sec 6) for an outline
  of what we want to prove.
-/

variable (T : Tnorm)

def IsNontrivial (p : I) := p ≠ 0 ∧ p ≠ 1

def StrictlyMonotone := ∀ p : I, p > 0 → ∀ q r : I, q < r → T.mul p q < T.mul p r

def Cancellative := ∀ p q r : I, T.mul p q = T.mul p r → (p = 0 ∨ q = r)

def ConditionalCancellative := ∀ p q r : I, T.mul p q = T.mul p r → T.mul p r > 0 → q = r

def IsArchimedean := ∀ p q : I, IsNontrivial p → IsNontrivial q → ∃ n : ℕ, T.npow n p < q

def HasLimitProperty := ∀ p : I, IsNontrivial p → Filter.Tendsto (fun n => (T.npow n p)) Filter.atTop (nhds 0)

-- Example 2.10 (ii)
lemma cond_canc_of_canc : Cancellative T → ConditionalCancellative T := by
  intro h p q r h2 h3
  apply h at h2
  obtain h0|heq := h2

  rw [h0] at h3
  simp only [Tnorm.zero_mul, gt_iff_lt, lt_self_iff_false] at h3

  exact heq

-- Proposition 2.11 (i)
lemma canc_iff_strictly_mono : Cancellative T ↔ StrictlyMonotone T := by
  constructor
  intro h p h2 q r h3

  have h4 : q ≠ r := by exact ne_of_lt h3
  apply le_of_lt at h3
  have h5 : T.mul p q ≤ T.mul p r := by exact T.mul_le_mul_left q r h3 p
  apply le_iff_eq_or_lt.mp at h5

  obtain heq|hlt := h5

  apply h at heq
  obtain hp0|heq2 := heq
  rw[hp0] at h2
  exact (StrictAnti.lt_iff_lt fun ⦃a b⦄ a ↦ h2).mp h2
  exact False.elim (h4 heq2)
  exact hlt


  intro h p q r h2
  by_cases h3 : q = r
  right; exact h3
  have hp : p ≥ 0 := by exact nonneg'
  apply le_iff_eq_or_lt.mp at hp

  obtain hp1|hp2 := hp
  symm at hp1
  left; exact hp1

  apply h at hp2
  right
  by_cases hle : q < r

  specialize hp2 q r
  apply hp2 at hle
  rw [h2] at hle
  apply (lt_self_iff_false (T.mul p r)).mp at hle
  contradiction

  apply not_lt_iff_eq_or_lt.mp at hle
  obtain hle1|hle2 := hle
  exact hle1
  specialize hp2 r q
  apply hp2 at hle2
  rw [h2] at hle2
  apply (lt_self_iff_false (T.mul p r)).mp at hle2
  contradiction



def HasNontrivialIdempotent := ∃ p : I, IsNontrivial p ∧ T.mul p p = p
def HasNilpotent := ∃ p : I, IsNontrivial p ∧ ∃ n : ℕ, T.npow n p = 0
def HasZeroDivisors := ∃ p q : I, p ≠ 0 ∧ q ≠ 0 ∧ T.mul p q = 0

-- Proposition 2.5
lemma nilpt_el_iff_zd : HasNilpotent T ↔ HasZeroDivisors T := by
  constructor
  intro h
  obtain ⟨p, hpnt, h⟩ := h
  let A := { n : ℕ | T.npow n p = 0}
  let n := sInf A
  have hpow := Nat.sInf_mem h
  have hn : n ≥ 1 := by
    refine Nat.one_le_iff_ne_zero.mpr ?_
    by_contra hn
    have hasd : (0:I) > 0 := by
      calc 0
        _ = T.npow n p := by exact (Eq.symm hpow)
        _ = 1 := by rw [hn, T.npow_zero]
        _ > 0 := zero_lt_one' ↑I
    exact (lt_self_iff_false 0).mp hasd
  use p
  use (T.npow (n-1) p)
  constructor
  exact hpnt.1
  constructor
  exact Nat.notMem_of_lt_sInf (Nat.sub_one_lt_of_lt hn)
  have hnpm : (n-1)+1 = n := by omega
  calc T.mul p (T.npow (n-1) p)
    _ = T.npow ((n-1)+1) p := by rfl
    _ = T.npow n p := by rw [hnpm]
    _ = 0 := hpow



  intro h
  obtain ⟨p, q, hp, hq, h⟩ := h
  use min p q; constructor; constructor
  apply unitInterval.pos_iff_ne_zero.mp
  apply lt_inf_iff.mpr
  constructor
  exact unitInterval.pos_iff_ne_zero.mpr hp
  exact unitInterval.pos_iff_ne_zero.mpr hq

  apply unitInterval.lt_one_iff_ne_one.mp
  apply inf_lt_iff.mpr
  by_cases h1 : p < 1
  left; exact h1
  right; push_neg at h1
  calc q
    _ = T.mul 1 q := by rw[T.one_mul q]
    _ ≤ T.mul p q := by apply T.mul_le_mul_right 1 p h1
    _ = 0 := h
    _ < 1 := zero_lt_one' ↑I

  use 2
  apply le_zero_iff.mp
  calc T.npow 2 (p ⊓ q)
    _ = T.mul (p ⊓ q) (p ⊓ q) := by rw[T.npow_two]
    _ ≤ T.mul p q := by apply T.mul_le_mul; apply min_le_left; apply min_le_right
    _ = 0 := h

-- Proposition 2.11 (ii)
lemma nntid_of_strictly_mono : StrictlyMonotone T → ¬ HasNontrivialIdempotent T := by
  intro h ⟨p, ⟨⟨hp0, hp1⟩, hp2⟩⟩
  specialize h p (unitInterval.pos_iff_ne_zero.mpr hp0) p 1 (unitInterval.lt_one_iff_ne_one.mpr hp1)
  rw [T.mul_one, hp2] at h
  exact (lt_self_iff_false p).mp h

-- Proposition 2.11 (iii)
lemma nzd_of_strictly_mono : StrictlyMonotone T → ¬ HasZeroDivisors T := by
  intro h ⟨p, q, ⟨hp, hq, hmul⟩⟩
  specialize h p (unitInterval.pos_iff_ne_zero.mpr hp) 0 q (unitInterval.pos_iff_ne_zero.mpr hq)
  rw [T.mul_zero, hmul] at h
  exact (lt_self_iff_false 0).mp h

lemma nzd_of_canc : Cancellative T → ¬ HasZeroDivisors T := by
  rw [canc_iff_strictly_mono]
  exact nzd_of_strictly_mono T

-- Remark 2.4(i)
lemma pow_idempt (p : I) (n : ℕ) : T.mul p p = p → T.npow (n+1) p = p := by
  intro h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [T.npow_succ, ih]
    exact h

lemma nntid_of_arch : IsArchimedean T → ¬ HasNontrivialIdempotent T := by
  intro h ⟨p, ⟨hp, hmul⟩⟩
  specialize h p p hp hp
  obtain ⟨n, hn⟩ := h
  by_cases hnn : n = 0
  rw [hnn, T.npow_zero] at hn
  apply lt_of_le_of_lt p.2.2 at hn
  exact (lt_self_iff_false p).mp hn


  have hnn : n-1+1=n := by omega
  apply pow_idempt T p (n-1) at hmul
  rw [hnn] at hmul
  rw [hmul] at hn
  exact (lt_self_iff_false p).mp hn


def Strict := T.Continuous ∧ StrictlyMonotone T

def Nilpotent := T.Continuous ∧ ∀ p : I, IsNontrivial p → ∃ n : ℕ, T.npow n p = 0



lemma half_mem_I : 1/2 ∈ I := by apply unitInterval.div_mem zero_le_one zero_le_two one_le_two
lemma half_nontrivial : IsNontrivial ⟨1/2, half_mem_I⟩ := by
  constructor
  refine coe_ne_zero.mp ?_; simp only [one_div, ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true]
  refine coe_ne_one.mp ?_; simp only [one_div, ne_eq, inv_eq_one, OfNat.ofNat_ne_one,
    not_false_eq_true]

lemma nilpt_el_of_nilpt : Nilpotent T → HasNilpotent T := by
  intro h
  use ⟨1/2, half_mem_I⟩
  constructor
  exact half_nontrivial
  apply And.right at h
  exact h ⟨1/2, half_mem_I⟩ half_nontrivial


lemma mono_mul_mono_mono (T : Tnorm) {x y : ℕ → I} (hx : Monotone x) (hy : Monotone y) :
  Monotone (fun n => T.mul (x n) (y n)) := by
    intro n m hnm
    apply T.mul_le_mul
    exact hx hnm
    exact hy hnm
lemma anti_mul_anti_anti (T : Tnorm) {x y : ℕ → I} (hx : Antitone x) (hy : Antitone y) :
  Antitone (fun n => T.mul (x n) (y n)) := by
    intro n m hnm
    apply T.mul_le_mul
    exact hx hnm
    exact hy hnm

lemma mono_lim_one (x : ℕ → I) (h : Antitone x) (h1 : Filter.Tendsto x Filter.atTop (nhds 1)) :
  ∀ n : ℕ, (x n) = 1 := by
    intro n
    by_contra hx
    push_neg at hx
    apply unitInterval.lt_one_iff_ne_one.mpr at hx
    have hx2 := Antitone.le_of_tendsto h h1 n
    have hxn := gt_of_ge_of_gt hx2 hx
    exact (lt_self_iff_false (x n)).mp hxn

-- Proposition 2.6
lemma idpt_iff_pow_seq_lim (h : T.RightContinuous) (a : I) : T.mul a a = a ↔ ∃ p : I,
  Filter.Tendsto (fun n => T.npow n p) Filter.atTop (nhds a) := by
    constructor; intro h; use a
    refine Metric.tendsto_atTop.mpr ?_
    intro ε he; use 1; intro n hn
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_one.mpr hn
    rw [hm, pow_idempt, dist_self]; exact he
    exact h

    intro hp
    obtain ⟨p, hp⟩ := hp
    have ha : Filter.Tendsto (fun n => T.mul (T.npow n p) (T.npow n p)) Filter.atTop (nhds a) := by
      apply Metric.tendsto_atTop.mpr
      apply Metric.tendsto_atTop.mp at hp
      intro ε he
      specialize hp ε he
      obtain ⟨N, hp⟩ := hp
      use N; intro n hn
      specialize hp (2*n) ?_
      omega
      rw [T.npow_add, ← Nat.two_mul]
      exact hp
    have hanti : Antitone (fun n => T.npow n p) := by
      intro n m hnm
      exact T.npow_le_self n m p hnm
    have hmul : Filter.Tendsto (fun n => T.mul (T.npow n p) (T.npow n p)) Filter.atTop (nhds (T.mul a a)) := by
      apply h
      exact hanti; exact hanti
      exact hp; exact hp
    exact tendsto_nhds_unique hmul ha


lemma arch_of_lp : HasLimitProperty T → IsArchimedean T := by
  intro h p q hpnt hqnt
  specialize h p hpnt
  apply Metric.tendsto_atTop.mp at h
  specialize h q (unitInterval.pos_iff_ne_zero.mpr hqnt.1)
  obtain ⟨N, h⟩ := h
  use N
  specialize h N ?_; rfl
  calc (T.npow N p).1
    _ = (T.npow N p).1 - 0 := by ring
    _ ≤ |(T.npow N p).1 - 0| := by apply le_abs_self
    _ < q := h

lemma lp_of_arch : IsArchimedean T → HasLimitProperty T := by
  intro h p hpnt
  apply Metric.tendsto_atTop.mpr
  intro ε he
  by_cases he1 : ε ≥ 1
  use 1; intro n hn
  calc |(T.npow n p).1-0|
    _ = |(T.npow n p).1| := by rw [sub_zero]
    _ = T.npow n p := abs_of_nonneg (nonneg (T.npow n p))
    _ ≤ p := by nth_rw 2 [← T.npow_one p]; apply T.npow_le_self; exact hn
    _ < 1 := by apply lt_of_le_of_ne (le_one p); refine coe_ne_one.mpr hpnt.2
    _ ≤ ε := he1
  push_neg at he1

  have heI : ε ∈ I := by constructor; exact le_of_lt he; exact le_of_lt he1
  specialize h p ⟨ε, heI⟩ hpnt ?_
  constructor
  apply unitInterval.pos_iff_ne_zero.mp he
  apply unitInterval.lt_one_iff_ne_one.mp he1
  obtain ⟨N, h⟩ := h
  use N; intro n hn
  calc |(T.npow n p).1-0|
    _ = |(T.npow n p).1| := by rw [sub_zero]
    _ = T.npow n p := abs_of_nonneg (nonneg (T.npow n p))
    _ ≤ T.npow N p := by exact T.npow_le_self N n p hn
    _ < ε := h

-- Theorem 2.12
lemma arch_iff_lp : IsArchimedean T ↔ HasLimitProperty T := by
  constructor
  exact lp_of_arch T
  exact arch_of_lp T

-- Proposition 2.15 (ii)
lemma arch_of_cont_cond_canc : T.RightContinuous → ConditionalCancellative T → IsArchimedean T := by
  intro hc hcc
  apply arch_of_lp
  intro p hpnt
  let x : ℕ → I := fun n => T.npow n p
  have hx : Antitone x := by
    intro n m hnm
    exact T.npow_le_self n m p hnm
  let a := ⨅ i, x i
  let ha := tendsto_atTop_iInf hx
  have haid : T.mul a a = a := by
    apply (idpt_iff_pow_seq_lim T hc a).mpr
    use p
  nth_rw 3 [← T.mul_one a] at haid
  specialize hcc a a 1 haid
  by_cases ha0 : a = 0
  unfold a at ha0; rw [ha0] at ha
  exact ha
  push_neg at ha0
  apply unitInterval.pos_iff_ne_zero.mpr at ha0
  rw [T.mul_one a] at hcc
  specialize hcc ha0
  unfold a at hcc; rw [hcc] at ha
  let hx1 : x 1 = 1 := (mono_lim_one x hx ha) 1
  unfold x at hx1
  rw [T.npow_one p] at hx1
  have hp : p ≠ 1 := hpnt.2
  contradiction

-- Proposition 2.15 (i)
lemma arch_of_cont_nntid : T.RightContinuous → ¬ HasNontrivialIdempotent T → IsArchimedean T := by
  intro hc h
  unfold HasNontrivialIdempotent at h; push_neg at h
  apply arch_of_lp
  intro p hpnt
  let x : ℕ → I := fun n => T.npow n p
  have hx : Antitone x := by
    intro n m hnm
    exact T.npow_le_self n m p hnm
  let hx2 := hx
  apply tendsto_atTop_iInf at hx
  let a := ⨅ i, x i
  have ha : T.mul a a = a := by
    apply (idpt_iff_pow_seq_lim T hc a).mpr
    use p
  specialize h a
  by_cases ha1 : a = 1
  unfold a at ha1; rw [ha1] at hx
  have hn : ∀ n : ℕ, (x n) = 1 := mono_lim_one x hx2 hx
  specialize hn 1
  have hp1 : p = 1 := by
    rw [← hn]; symm
    exact Tnorm.npow_one p
  have hp2 : p ≠ 1 := hpnt.2
  contradiction

  by_cases ha0 : a = 0
  unfold a at ha0; rw [ha0] at hx
  exact hx
  push_neg at ha0; push_neg at ha1
  have hant : IsNontrivial a := by constructor; exact ha0; exact ha1
  specialize h hant
  contradiction

-- Proposition 2.15 (iv)
lemma arch_of_strict : Strict T → IsArchimedean T := by
  intro h
  obtain ⟨h1, h2⟩ := h
  apply arch_of_cont_nntid
  exact Tnorm.right_cont_of_cont T h1
  apply nntid_of_strictly_mono T h2

-- Proposition 2.15 (v)
lemma arch_of_all_nilpt_els : (∀ p : I, IsNontrivial p → ∃ n : ℕ, T.npow n p = 0) → IsArchimedean T := by
  intro h
  intro p q hpnt hqnt
  specialize h p hpnt
  obtain ⟨n, h⟩ := h
  use n
  apply And.left at hqnt
  apply unitInterval.pos_iff_ne_zero.mpr at hqnt
  rw [h]; exact hqnt

-- The next three theorems encompass the result of Theorem 2.18
theorem nilpt_of_cont_arch_zd (T : Tnorm) : T.Continuous → IsArchimedean T → HasZeroDivisors T → Nilpotent T := by
  intro hc h hzd
  constructor
  exact hc
  apply (nilpt_el_iff_zd T).mpr at hzd
  obtain ⟨a, hant, n, hpow⟩ := hzd
  intro p hpnt

  specialize h p a hpnt hant
  obtain ⟨m, harch⟩ := h
  use (m*n)
  rw [mul_comm]
  rw [← T.npow_mul]
  apply le_zero_iff.mp
  calc T.npow n (T.npow m p)
    _ ≤ T.npow n a := by apply T.npow_le n (T.npow m p) a (le_of_lt harch)
    _ = 0 := hpow

theorem strict_of_cont_arch_nzd (T : Tnorm) : T.Continuous → IsArchimedean T → ¬ HasZeroDivisors T → Strict T := by
  intro hc harch h
  contrapose! h
  unfold Strict at h; push_neg at h
  specialize h hc
  unfold StrictlyMonotone at h; push_neg at h
  obtain ⟨p, hp, q, r, hqr, hmul⟩ := h
  let hmul2 := T.mul_le_mul_left q r (le_of_lt hqr) p
  have heq : T.mul p r = T.mul p q := by apply antisymm hmul hmul2
  have hqrr : T.mul q r < T.mul 1 r := by
    calc T.mul q r
      _ ≤ q := T.mul_le_left q r
      _ < r := hqr
      _ = T.mul 1 r := by symm; exact T.one_mul r
  have hz : ∃ z : I, T.mul z r = q := by
    have hrc : Continuous (fun (z : I) => T.mul z r) := Continuous.uncurry_right r ((cont_def T).mp hc)
    apply intermediate_value_univ q 1 at hrc
    suffices q ∈ Set.Icc (T.mul q r) (T.mul 1 r) by
      apply hrc at this
      apply Set.mem_range.mp at this
      exact this
    constructor
    exact T.mul_le_left q r
    rw [T.one_mul]; exact le_of_lt hqr
  obtain ⟨z, hz⟩ := hz
  have hzpow : ∀ n : ℕ, T.mul p r = T.mul (T.mul p r) (T.npow n z) := by
    intro n
    induction' n with n ih
    rw [T.npow_zero, T.mul_one]

    calc T.mul p r
      _ = T.mul p q := heq
      _ = T.mul p (T.mul z r) := by rw[hz]
      _ = T.mul p (T.mul r z) := by nth_rw 2 [T.mul_comm]
      _ = T.mul (T.mul p r) z := by rw [T.mul_assoc]
      _ = T.mul (T.mul (T.mul p r) (T.npow n z)) z := by rw [← ih]
      _ = T.mul (T.mul p r) (T.mul (T.npow n z) z) := by rw [← T.mul_assoc]
      _ = T.mul (T.mul p r) (T.npow (n+1) z) := by nth_rw 3 [T.mul_comm]; rw [← T.npow_succ]
  use p; use r
  constructor
  exact unitInterval.pos_iff_ne_zero.mp hp
  constructor
  apply unitInterval.pos_iff_ne_zero.mp
  exact lt_of_le_of_lt (nonneg q) hqr

  have hlim : Filter.Tendsto (fun n => T.mul (T.mul p r) (T.npow n z)) Filter.atTop (nhds (T.mul p r)) := by
    have hfun : (fun n => T.mul p r) = (fun n => T.mul (T.mul p r) (T.npow n z)) := by
      ext n; exact congrArg Subtype.val (hzpow n)
    rw [← hfun]
    exact tendsto_const_nhds
  by_cases hz0 : z = 0
  rw [hz0, T.zero_mul] at hz
  rw [← hz, T.mul_zero] at heq
  exact heq

  specialize hc (fun n => T.mul p r) (fun n => T.npow n z) (T.mul p r) 0 tendsto_const_nhds ?_
  apply lp_of_arch at harch
  specialize harch z
  apply harch

  constructor
  exact hz0
  by_contra hz1
  rw [hz1, T.one_mul] at hz
  apply ne_of_lt at hqr
  symm at hz
  contradiction

  rw [T.mul_zero] at hc
  exact tendsto_nhds_unique hlim hc

theorem nilpt_or_strict_of_cont_arch (T : Tnorm) : T.Continuous → IsArchimedean T → (Nilpotent T ∨ Strict T) := by
  intro hc  harch
  by_cases hzd : HasZeroDivisors T
  left; exact nilpt_of_cont_arch_zd T hc harch hzd
  right; exact strict_of_cont_arch_nzd T hc harch hzd


lemma arch_of_nilpt : Nilpotent T → IsArchimedean T := by
  intro h
  apply arch_of_all_nilpt_els
  apply And.right at h
  exact h

lemma nntid_of_nilpt : Nilpotent T → ¬ HasNontrivialIdempotent T := by
  intro h
  apply arch_of_nilpt at h
  apply nntid_of_arch at h
  exact h
