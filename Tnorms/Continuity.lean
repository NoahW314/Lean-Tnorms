import Tnorms.Defs
import Tnorms.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Sequences
import Tnorms.SupInfI

open unitInterval


theorem cont_def (T : Tnorm) : T.Continuous ↔ Continuous (Function.uncurry T.mul) := by
  constructor
  intro h
  apply continuous_iff_continuousAt.mpr
  intro (p, q)
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro u hu

  apply (Prod.tendsto_iff u (p,q)).mp at hu
  specialize h (fun n => (u n).1) (fun n => (u n).2) p q hu.1 hu.2
  exact h

  intro h
  intro x y p q hx hy
  let u : ℕ → I × I := fun n => ((x n), (y n))
  apply continuous_iff_seqContinuous.mp at h
  unfold SeqContinuous at h
  specialize h (Filter.Tendsto.prodMk_nhds hx hy)
  exact h


lemma mono_of_conv {x : ℕ → I} {p : I} (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
  ∃ a : ℕ → I, Monotone a ∧ (∀ n : ℕ, (a n) ≤ (x n)) ∧ Filter.Tendsto a Filter.atTop (nhds p) := by
    have hsnoe : ∀ n : ℕ, (x '' {m : ℕ | m ≥ n}).Nonempty := by
      intro n
      apply Set.image_nonempty.mpr
      use n; simp only [ge_iff_le, Set.mem_setOf_eq, le_refl]
    let a : ℕ → I := fun n => sInf (x '' {m : ℕ | m ≥ n})
    use a
    constructor
    · intro n k hnk
      apply sInf_le_sInf

      apply Set.image_subset_iff.mpr
      intro q hq
      simp at hq
      simp only [ge_iff_le, Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
      use q; constructor
      apply le_trans hnk hq; rfl
    constructor
    · intro n
      apply sInf_le
      simp only [ge_iff_le, Set.mem_image, Set.mem_setOf_eq]
      use n
    · refine Metric.tendsto_atTop.mpr ?_
      intro ε he

      apply Metric.tendsto_atTop.mp at hx
      specialize hx (ε/2) (half_pos he)
      obtain ⟨N, hx⟩ := hx
      use N
      intro n hn

      have hanrfl : (a n) ≤ (a n) := by rfl
      let han := (UnitInterval.sInf_le_iff (hsnoe n)).mp hanrfl (ε/2) (half_pos he)
      obtain ⟨q, hq, han⟩ := han
      simp at hq
      obtain ⟨m, hm, hq⟩ := hq
      rw [← hq] at han

      specialize hx m ?_
      exact Nat.le_trans hn hm

      have hax : |(a n)-(x m).1| < (ε/2) := by
        apply max_lt
        calc (a n).1-(x m)
          _ ≤ 0 := by
            apply tsub_nonpos.mpr
            apply Subtype.coe_le_coe.mpr; apply sInf_le
            simp only [ge_iff_le, Set.mem_image, Set.mem_setOf_eq]; use m
          _ < ε/2 := by exact half_pos he
        rw [neg_sub]
        exact sub_left_lt_of_lt_add han
      calc |(a n)-p.1|
        _ ≤ |(a n)-(x m).1|+|(x m)-p.1| := by apply abs_sub_le
        _ < |(a n)-(x m).1|+(ε/2) := by exact (Real.add_lt_add_iff_left |↑(a n) - ↑(x m)|).mpr hx
        _ < (ε/2)+(ε/2) := by apply (add_lt_add_iff_right (ε/2)).mpr hax
        _ = ε := by apply add_halves


lemma anti_of_conv {x : ℕ → I} {p : I} (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
  ∃ a : ℕ → I, Antitone a ∧ (∀ n : ℕ, (x n) ≤ (a n)) ∧ Filter.Tendsto a Filter.atTop (nhds p) := by
    let x' : ℕ → I := σ ∘ x
    let ha := mono_of_conv (continuous_iff_seqContinuous.mp continuous_symm hx)
    obtain ⟨a', ha⟩ := ha
    use σ ∘ a'
    constructor
    intro n m hnm
    apply symm_le_symm.mpr
    exact ha.1 hnm

    constructor
    intro n
    apply le_symm_comm.mpr
    exact ha.2.1 n

    rw [← symm_symm p]
    apply continuous_iff_seqContinuous.mp continuous_symm
    exact ha.2.2

theorem cont_both_vars {T : Tnorm} : T.Continuous ↔
  (∀ p : I, Continuous (fun q : I => T.mul p q)) ∧ (∀ p : I, Continuous (fun q : I => T.mul q p)) := by
    constructor
    intro h
    constructor
    · intro p
      apply continuous_iff_seqContinuous.mpr
      intro y q hy
      apply h (fun n => p) y p q (tendsto_const_nhds) hy
    · intro p
      apply continuous_iff_seqContinuous.mpr
      intro x q hx
      apply h x (fun n => p) q p hx (tendsto_const_nhds)

    intro h
    intro x y p q hx hy
    apply Metric.tendsto_atTop.mpr
    intro ε he

    let ha := mono_of_conv hx
    let hb := anti_of_conv hx
    let hc := mono_of_conv hy
    let hd := anti_of_conv hy
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    obtain ⟨c, hc⟩ := hc
    obtain ⟨d, hd⟩ := hd

    let h1 := h.1 p

    apply continuous_iff_seqContinuous.mp at h1

    let hc1 := h1 (hc.2).2
    let hd1 := h1 (hd.2).2
    apply Metric.tendsto_atTop.mp at hc1
    apply Metric.tendsto_atTop.mp at hd1
    specialize hc1 (ε/2) (half_pos he)
    specialize hd1 (ε/2) (half_pos he)
    obtain ⟨N₁, hc1⟩ := hc1
    obtain ⟨N₂, hd1⟩ := hd1
    simp only [Function.comp_apply] at hc1
    simp only [Function.comp_apply] at hd1

    let N := N₁ ⊔ N₂
    let hc2 := h.2 (c N)
    let hd2 := h.2 (d N)


    apply continuous_iff_seqContinuous.mp at hc2
    apply continuous_iff_seqContinuous.mp at hd2
    let ha1 := hc2 (ha.2).2
    let hb1 := hd2 (hb.2).2
    apply Metric.tendsto_atTop.mp at ha1
    apply Metric.tendsto_atTop.mp at hb1
    specialize ha1 (ε/2) (half_pos he)
    specialize hb1 (ε/2) (half_pos he)
    obtain ⟨M₁, ha1⟩ := ha1
    obtain ⟨M₂, hb1⟩ := hb1
    simp only [Function.comp_apply] at ha1
    simp only [Function.comp_apply] at hb1

    let K := N ⊔ M₁ ⊔ M₂
    use K
    intro k hk
    have hNk : N ≤ k := calc N
      _ ≤ N ⊔ M₁ := by exact Nat.le_max_left N M₁
      _ ≤ k := by exact le_of_max_le_left hk
    have hMk : M₁ ≤ k := calc M₁
      _ ≤ N ⊔ M₁ := by exact le_max_right N M₁
      _ ≤ k := by exact le_of_max_le_left hk
    apply sup_lt_iff.mpr
    constructor
    apply sub_lt_iff_lt_add.mpr
    calc (T.mul (x k) (y k)).1
      _ ≤ T.mul (b M₂) (y k) := by apply T.mul_le_mul_right; calc
            x k
            _ ≤ b k := by apply hb.2.1 k
            _ ≤ b M₂ := by apply hb.1 (le_of_max_le_right hk)
      _ ≤ T.mul (b M₂) (d N) := by apply T.mul_le_mul_left; calc
            y k
            _ ≤ d k := by apply hd.2.1 k
            _ ≤ d N := by apply hd.1 hNk
      _ < (ε/2)+T.mul p (d N)  := by
          specialize hb1 M₂ ?_; rfl
          apply max_lt_iff.mp at hb1
          exact sub_lt_iff_lt_add.mp hb1.1
      _ < (ε/2)+((ε/2)+T.mul p q) := by
          refine add_lt_add_left ?_ (ε / 2)
          specialize hd1 N ?_
          exact le_max_right N₁ N₂
          apply max_lt_iff.mp at hd1
          exact sub_lt_iff_lt_add.mp hd1.1
      _ = ε+T.mul p q := by ring

    simp
    apply sub_lt_comm.mp
    calc (T.mul p q).1 - ε
      _ = (T.mul p q)-(ε/2)-(ε/2) := by ring
      _ < T.mul p (c N) - (ε/2) := by
          apply sub_lt_sub_right ?_
          specialize hc1 N ?_
          exact le_max_left N₁ N₂
          apply max_lt_iff.mp at hc1
          rw [neg_sub] at hc1
          exact sub_lt_comm.mp hc1.2
      _ < T.mul (a M₁) (c N) := by
          specialize ha1 M₁ ?_; rfl
          apply max_lt_iff.mp at ha1
          rw [neg_sub] at ha1
          exact sub_lt_comm.mp ha1.2
      _ ≤ T.mul (a M₁) (y k) := by
          apply T.mul_le_mul_left
          calc c N
            _ ≤ c k := by exact hc.1 hNk
            _ ≤ y k := by exact hc.2.1 k
      _ ≤ T.mul (x k) (y k) := by
          apply T.mul_le_mul_right
          calc a M₁
            _ ≤ a k := by exact ha.1 hMk
            _ ≤ x k := by exact ha.2.1 k


theorem cont_one_var (T : Tnorm) : T.Continuous ↔
  ∀ p : I, Continuous (fun q : I => T.mul p q) := by
    constructor
    intro h
    apply cont_both_vars.mp at h
    exact h.1

    intro h
    apply cont_both_vars.mpr
    constructor
    exact h
    intro p
    specialize h p
    have hfun : ∀ q : I, (fun q => T.mul p q) q = (fun q => T.mul q p) q := by intro q; exact T.mul_comm p q
    apply (continuous_congr hfun).mp
    exact h

theorem cont_iff_left_right (T : Tnorm) : T.Continuous ↔ (T.LeftContinuous ∧ T.RightContinuous) := by
  constructor
  intro h
  constructor
  exact T.left_cont_of_cont h
  exact T.right_cont_of_cont h

  intro ⟨hl, hr⟩
  intro x y p q hx hy

  let ⟨a, ha⟩ := mono_of_conv hx; let ⟨b, hb⟩ := anti_of_conv hx
  let ⟨c, hc⟩ := mono_of_conv hy; let ⟨d, hd⟩ := anti_of_conv hy

  let hbel := hl a c p q ha.1 hc.1 ha.2.2 hc.2.2
  let habo := hr b d p q hb.1 hd.1 hb.2.2 hd.2.2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hbel habo

  intro n; simp
  apply T.mul_le_mul
  exact ha.2.1 n; exact hc.2.1 n

  intro n; simp
  apply T.mul_le_mul
  exact hb.2.1 n; exact hd.2.1 n
