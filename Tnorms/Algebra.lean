import Tnorms.Defs
import Tnorms.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Data.Real.Basic

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


lemma cond_canc_of_canc : Cancellative T → ConditionalCancellative T := by
  intro h
  intro p q r
  intro h2
  intro h3
  apply h at h2

  obtain h0|heq := h2

  rw [h0] at h3
  simp at h3

  exact heq

lemma canc_iff_strictly_mono : Cancellative T ↔ StrictlyMonotone T := by
  constructor
  intro h
  intro p
  intro h2
  intro q r
  intro h3

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


  intro h
  intro p q r
  intro h2
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
        _ > 0 := by exact zero_lt_one' ↑I
    exact (lt_self_iff_false 0).mp hasd
  use p
  use (T.npow (n-1) p)
  constructor
  exact hpnt.1
  constructor
  exact Nat.not_mem_of_lt_sInf (Nat.sub_one_lt_of_lt hn)
  have hnpm : (n-1)+1 = n := by omega
  calc T.mul p (T.npow (n-1) p)
    _ = T.npow ((n-1)+1) p := by rfl
    _ = T.npow n p := by rw [hnpm]
    _ = 0 := hpow



  intro h
  obtain ⟨p, q, hp, hq, h⟩ := h
  use min p q
  constructor
  constructor
  apply unitInterval.pos_iff_ne_zero.mp
  apply lt_inf_iff.mpr
  constructor
  exact unitInterval.pos_iff_ne_zero.mpr hp
  exact unitInterval.pos_iff_ne_zero.mpr hq

  apply unitInterval.lt_one_iff_ne_one.mp
  apply inf_lt_iff.mpr
  by_cases h1 : p < 1
  left; exact h1
  right;
  push_neg at h1
  calc q
    _ = T.mul 1 q := by rw[T.one_mul q]
    _ ≤ T.mul p q := by apply T.mul_le_mul_right 1 p h1
    _ = 0 := by exact h
    _ < 1 := by exact zero_lt_one' ↑I

  use 2
  apply le_zero_iff.mp
  calc T.npow 2 (p ⊓ q)
    _ = T.mul (p ⊓ q) (T.mul (p ⊓ q) 1) := by rfl
    _ = T.mul (p ⊓ q) (p ⊓ q) := by rw[T.mul_one (p ⊓ q)]
    _ ≤ T.mul p q := by apply T.mul_le_mul; apply min_le_left; apply min_le_right
    _ = 0 := h




lemma nntid_of_strictly_mono : StrictlyMonotone T → ¬ HasNontrivialIdempotent T := by
  intro h
  intro h2
  obtain ⟨p, hp⟩ := h2
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hp0, hp1⟩ := hp1
  specialize h p
  have hp02 : p > 0 := by exact unitInterval.pos_iff_ne_zero.mpr hp0
  specialize h hp02
  specialize h p 1
  have hp12 : p < 1 := by exact unitInterval.lt_one_iff_ne_one.mpr hp1
  specialize h hp12
  simp at h
  rw [hp2] at h
  exact (lt_self_iff_false p).mp h

lemma nzd_of_strictly_mono : StrictlyMonotone T → ¬ HasZeroDivisors T := by
  intro h
  intro h2
  obtain ⟨p, q, hpq⟩ := h2
  obtain ⟨hp, hq, hmul⟩ := hpq
  specialize h p
  have hp0 : p > 0 := by exact unitInterval.pos_iff_ne_zero.mpr hp
  specialize h hp0 0 q
  have hq0 : q > 0 := by exact unitInterval.pos_iff_ne_zero.mpr hq
  specialize h hq0
  simp at h
  rw [hmul] at h
  exact (lt_self_iff_false 0).mp h

lemma nzd_of_canc : Cancellative T → ¬ HasZeroDivisors T := by
  intro h
  intro h2
  obtain ⟨p, q, hpq⟩ := h2
  obtain ⟨hp, hq, hmul⟩ := hpq
  specialize h p q 0
  simp at h
  specialize h hmul
  obtain h1|h2 := h
  apply hp; exact h1
  apply hq; exact h2

lemma pow_idempt (p : I) (n : ℕ) : T.mul p p = p → T.npow (n+1) p = p := by
  intro h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [T.npow_succ, ih]
    exact h



lemma nntid_of_arch : IsArchimedean T → ¬ HasNontrivialIdempotent T := by
  intro h
  intro h2
  obtain ⟨p, hp⟩ := h2
  obtain ⟨hp, hmul⟩ := hp
  specialize h p p hp hp
  obtain ⟨n, hn⟩ := h
  by_cases hnn : n = 0

  rw [hnn] at hn
  simp at hn
  have hp1 : p ≤ 1 := by exact le_one p
  have h11 : 1 < 1 := by exact lt_imp_lt_of_le_imp_le (fun a ↦ hp1) hn
  exact (lt_self_iff_false 1).mp h11

  have hnn : n-1+1=n := by omega

  apply pow_idempt T p (n-1) at hmul
  rw [hnn] at hmul
  rw [hmul] at hn
  exact (lt_self_iff_false p).mp hn


def Strict := T.Continuous ∧ StrictlyMonotone T

def Nilpotent := T.Continuous ∧ ∀ p : I, IsNontrivial p → ∃ n : ℕ,
  T.npow n p = 0



lemma half_mem_I : 1/2 ∈ I := by apply unitInterval.div_mem; simp;simp;simp
lemma half_nontrivial : IsNontrivial ⟨1/2, half_mem_I⟩ := by
  constructor
  refine coe_ne_zero.mp ?_; simp
  refine coe_ne_one.mp ?_; simp

lemma nilpt_el_of_nilpt : Nilpotent T → HasNilpotent T := by
  intro h
  use ⟨1/2, half_mem_I⟩
  constructor
  exact half_nontrivial
  apply And.right at h
  exact h ⟨1/2, half_mem_I⟩ half_nontrivial


lemma arch_of_nilpt : Nilpotent T → IsArchimedean T := by
  intro h
  intro p q hpnt hqnt
  apply And.right at h
  specialize h p hpnt
  obtain ⟨n, hn⟩ := h
  use n
  calc T.npow n p
    _ = 0 := by exact hn
    _ < q := by apply unitInterval.pos_iff_ne_zero.mpr hqnt.left

lemma nntid_of_nilpt : Nilpotent T → ¬ HasNontrivialIdempotent T := by
  intro h
  apply arch_of_nilpt at h
  apply nntid_of_arch at h
  exact h


-- I shouldn't have to prove this, but the mathlib implementation doesn't seem to work
theorem monotone_convergence (x : ℕ → I) (h : Antitone x) : ∃ a : I, Filter.Tendsto x Filter.atTop (nhds a) := by
  use ⟨sInf (Subtype.val '' Set.range x), inf_mem_I⟩
  refine Metric.tendsto_atTop.mpr ?_
  intro ε he
  have hnonem : (Subtype.val '' Set.range x).Nonempty := by
    apply Set.image_nonempty.mpr
    exact Set.range_nonempty x
  let hs := Real.lt_sInf_add_pos hnonem he
  obtain ⟨p, hp, hs⟩ := hs
  simp at hp
  obtain ⟨N, hN⟩ := hp
  rw [← hN] at hs
  use N
  intro n hn
  apply abs_sub_lt_iff.mpr
  constructor
  refine sub_left_lt_of_lt_add ?_
  calc (x n).1
    _ ≤ (x N).1 := h hn
    _ < sInf (Subtype.val '' Set.range x)+ε := hs

  calc sInf (Subtype.val '' Set.range x) - (x n)
    _ ≤ 0 := by
      simp; refine csInf_le ?_ ?_
      apply bddBelow_def.mpr
      use 0; intro p
      simp; intro m hm
      rw [← hm]
      exact nonneg (x m)
      simp
    _ < ε := he


lemma lim_le_anti {x : ℕ → I} {p : I} (h : Antitone x) (h1 : Filter.Tendsto x Filter.atTop (nhds p)) :
  ∀ n : ℕ, p ≤ (x n) := by
    intro n
    by_contra hx
    apply Metric.tendsto_atTop.mp at h1
    push_neg at hx
    specialize h1 (p - (x n)) ?_
    simp [hx]
    obtain ⟨N, h1⟩ := h1
    specialize h1 (N ⊔ n) ?_
    exact le_max_left N n
    have h2 : p-(x (N ⊔ n)) < p - (x n).1 := by
      calc p-(x (N ⊔ n)).1
        _ ≤ |p-(x (N ⊔ n)).1| := by apply le_abs_self
        _ = |(x (N ⊔ n)).1-p| := by apply abs_sub_comm
        _ < p-(x n) := h1
    simp at h2
    apply not_le_of_lt at h2
    specialize h (le_max_right N n)
    contradiction

lemma mono_lim_one (x : ℕ → I) (h : Antitone x) (h1 : Filter.Tendsto x Filter.atTop (nhds 1)) :
  ∀ n : ℕ, (x n) = 1 := by
    intro n
    by_contra hx
    push_neg at hx
    apply unitInterval.lt_one_iff_ne_one.mpr at hx
    have hx2 := lim_le_anti h h1 n
    have hxn := gt_of_ge_of_gt hx2 hx
    exact (lt_self_iff_false (x n)).mp hxn

lemma idpt_iff_pow_seq_lim (h : T.RightContinuous) (a : I) : T.mul a a = a ↔ ∃ p : I,
  Filter.Tendsto (fun n => T.npow n p) Filter.atTop (nhds a) := by
    constructor
    intro h
    use a
    refine Metric.tendsto_atTop.mpr ?_
    intro ε he
    use 1
    intro n hn
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_one.mpr hn
    rw [hm]
    rw [pow_idempt]
    simp [he]
    exact h

    intro hp
    obtain ⟨p, hp⟩ := hp
    have ha : Filter.Tendsto (fun n => T.mul (T.npow n p) (T.npow n p)) Filter.atTop (nhds a) := by
      apply Metric.tendsto_atTop.mpr
      apply Metric.tendsto_atTop.mp at hp
      intro ε he
      specialize hp ε he
      obtain ⟨N, hp⟩ := hp
      use N
      intro n hn
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
  intro h
  intro p q hpnt hqnt
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

lemma arch_of_cont_cond_canc : T.RightContinuous → ConditionalCancellative T → IsArchimedean T := by
  intro hc hcc
  apply arch_of_lp
  intro p hpnt
  let x : ℕ → I := fun n => T.npow n p
  have hx : Antitone x := by
    intro n m hnm
    exact T.npow_le_self n m p hnm
  let ha := monotone_convergence x hx
  obtain ⟨a, ha⟩ := ha
  have haid : T.mul a a = a := by
    apply (idpt_iff_pow_seq_lim T hc a).mpr
    use p
  nth_rw 3 [← T.mul_one a] at haid
  specialize hcc a a 1 haid
  by_cases ha0 : a = 0
  rw [ha0] at ha
  exact ha
  push_neg at ha0
  apply unitInterval.pos_iff_ne_zero.mpr at ha0
  rw [T.mul_one a] at hcc
  specialize hcc ha0
  rw [hcc] at ha
  let hx1 : x 1 = 1 := (mono_lim_one x hx ha) 1
  unfold x at hx1
  rw [T.npow_one p] at hx1
  have hp : p ≠ 1 := hpnt.2
  contradiction


lemma arch_of_cont_nntid : ¬ HasNontrivialIdempotent T → T.RightContinuous → IsArchimedean T := by
  intro h hc
  unfold HasNontrivialIdempotent at h; push_neg at h
  apply arch_of_lp
  intro p hpnt
  let x : ℕ → I := fun n => T.npow n p
  have hx : Antitone x := by
    intro n m hnm
    exact T.npow_le_self n m p hnm
  let hx2 := hx
  apply monotone_convergence x at hx
  obtain ⟨a, hx⟩ := hx
  have ha : T.mul a a = a := by
    apply (idpt_iff_pow_seq_lim T hc a).mpr
    use p
  specialize h a
  by_cases ha1 : a = 1
  rw [ha1] at hx
  have hn : ∀ n : ℕ, (x n) = 1 := mono_lim_one x hx2 hx
  specialize hn 1
  have hp1 : p = 1 := by
    rw [← hn]
    exact Eq.symm (Tnorm.npow_one p)
  have hp2 : p ≠ 1 := hpnt.2
  contradiction

  by_cases ha0 : a = 0
  rw [ha0] at hx
  exact hx
  push_neg at ha0; push_neg at ha1
  have hant : IsNontrivial a := by constructor; exact ha0; exact ha1
  specialize h hant
  contradiction


lemma arch_of_strict : Strict T → IsArchimedean T := by
  intro h
  obtain ⟨h1, h2⟩ := h
  apply arch_of_cont_nntid
  apply nntid_of_strictly_mono T h2
  exact Tnorm.right_cont_of_cont T h1


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
