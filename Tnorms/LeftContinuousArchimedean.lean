import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Algebra
import Tnorms.Continuity
import Tnorms.LeftContinuity

import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.Order.Ring.Star

open unitInterval

theorem right_cont_boundary (T : Tnorm) (p q : I) : ¬ IsNontrivial p → ∀ x y : ℕ → I,
  Antitone x → Antitone y
  → Filter.Tendsto x Filter.atTop (nhds p)
  → Filter.Tendsto y Filter.atTop (nhds q)
  → Filter.Tendsto (fun n => T.mul (x n) (y n)) Filter.atTop (nhds (T.mul p q)) := by
    intro hpt x y hax hay hx hy
    unfold IsNontrivial at hpt; push_neg at hpt
    by_cases hp : p ≠ 0
    apply hpt at hp
    rw [hp] at hx
    have hxn : x = (fun n => 1) := by
      ext n
      apply Subtype.eq_iff.mp
      exact mono_lim_one x hax hx n
    simp [hxn, hp]
    exact hy

    push_neg at hp
    simp [hp]
    rw [hp] at hx
    apply Metric.tendsto_atTop.mpr
    apply Metric.tendsto_atTop.mp at hx
    intro ε he
    specialize hx ε he
    obtain ⟨N, hx⟩ := hx
    use N
    intro n hn
    specialize hx n hn
    calc |(T.mul (x n) (y n)).1-0|
      _ = |(T.mul (x n) (y n)).1| := by rw [sub_zero]
      _ = T.mul (x n) (y n) := by apply abs_of_nonneg (nonneg (T.mul (x n) (y n)))
      _ ≤ (x n) ⊓ (y n) := by apply T.mul_le_min
      _ ≤ (x n) := by apply Subtype.coe_le_coe.mpr; exact min_le_left (x n) (y n)
      _ = |(x n).1| := by apply Eq.symm (abs_of_nonneg (nonneg (x n)))
      _ = |(x n).1-0| := by rw [sub_zero]
      _ < ε := hx


theorem right_cont_boundary' (T : Tnorm) (p q : I) : ¬ IsNontrivial q → ∀ x y : ℕ → I,
  Antitone x → Antitone y
  → Filter.Tendsto x Filter.atTop (nhds p)
  → Filter.Tendsto y Filter.atTop (nhds q)
  → Filter.Tendsto (fun n => T.mul (x n) (y n)) Filter.atTop (nhds (T.mul p q)) := by
    intro hq x y hax hay hx hy
    have hfun : (fun n => T.mul (x n) (y n)) = (fun n => T.mul (y n) (x n)) := by
      ext n
      rw [T.mul_comm]
    rw [T.mul_comm, hfun]
    exact right_cont_boundary T q p hq y x hay hax hy hx



lemma zero_one_arch {T : Tnorm} (h : IsArchimedean T) (p q : I) : p ≠ 1 → q ≠ 0 → ∃ n, T.npow n p < q := by
  intro hp1 hq0
  by_cases hp0 : p ≠ 0
  by_cases hq1 : q ≠ 1

  apply h p q
  constructor; exact hp0; exact hp1
  constructor; exact hq0; exact hq1

  push_neg at hq1
  use 1
  rw [hq1, T.npow_one]
  exact unitInterval.lt_one_iff_ne_one.mpr hp1

  push_neg at hp0
  use 1
  rw [hp0, T.npow_one]
  exact unitInterval.pos_iff_ne_zero.mpr hq0

lemma pow_set_nonempty {T : Tnorm} (p q : I) : q ≠ 1 → {m | T.npow m p > q}.Nonempty := by
  intro hq
  use 0; simp
  exact unitInterval.lt_one_iff_ne_one.mpr hq
lemma pow_set_bddAbove {T : Tnorm} (p q : I) : p ≠ 1 → q ≠ 0 → IsArchimedean T → BddAbove {m | T.npow m p > q} := by
  intro hp hq h
  have h : ∃ n, T.npow n p ≤ q := by
      obtain ⟨n, hn⟩ := (zero_one_arch h p q hp hq)
      use n
      exact le_of_lt hn
  refine bddAbove_def.mpr ?_
  obtain ⟨n, h⟩ := h
  use n
  intro m
  contrapose
  intro hm
  push_neg at hm
  simp
  calc T.npow m p
    _ ≤ T.npow n p := by apply T.npow_le_self n m p (le_of_lt hm)
    _ ≤ q := h


lemma seq_arch {T : Tnorm} {z : ℕ → I} {p : I} {n : ℕ} (h : IsArchimedean T) (hz : ∀ n : ℕ, (z n) ≠ 1)
  (hp : p ≠ 0) : T.npow (((fun n => sSup { m : ℕ | T.npow m (z n) > p}) n)+1) (z n) ≤ p := by
    apply le_of_not_lt
    apply notMem_of_csSup_lt (lt_add_one (sSup {m | T.npow m (z n) > p})) (pow_set_bddAbove (z n) p (hz n) hp h)

theorem mul_lim_le_lim_mul (T : Tnorm) {x y : ℕ → I} {p q a : I} (hax : Antitone x) (hay : Antitone y)
  (hx : Filter.Tendsto x Filter.atTop (nhds p)) (hy : Filter.Tendsto y Filter.atTop (nhds q))
  (hmul : Filter.Tendsto (fun n => T.mul (x n) (y n)) Filter.atTop (nhds a)) :
  T.mul p q ≤ a := by
    by_contra h
    push_neg at h

    let ε := (T.mul p q).1 - a
    have he : ε > 0 := by exact sub_pos.mpr h
    apply Metric.tendsto_atTop.mp at hmul
    specialize hmul ε he
    obtain ⟨n, hmul⟩ := hmul
    specialize hmul n ?_; rfl

    have hxn := Antitone.le_of_tendsto hax hx n
    have hyn := Antitone.le_of_tendsto hay hy n

    have hxyn : T.mul (x n) (y n) < T.mul (x n) (y n) := by
      calc (T.mul (x n) (y n)).1
        _ < a+ε := by refine lt_add_of_sub_left_lt ?_; exact lt_of_abs_lt hmul
        _ = T.mul p q := by unfold ε; apply add_sub_cancel
        _ ≤ T.mul (x n) (y n) := by apply T.mul_le_mul; exact hxn; exact hyn

    exact (lt_self_iff_false (T.mul (x n) (y n))).mp hxyn



theorem cont_of_left_cont_arch (T : LeftContinuousTnorm) : IsArchimedean T.toTnorm → T.Continuous := by
  intro h
  apply (cont_iff_left_right T.toTnorm).mpr
  constructor
  exact T.left_cont
  by_contra hc
  unfold Tnorm.RightContinuous at hc
  push_neg at hc
  obtain ⟨x, y, p, q, hax, hay, hx, hy, hc⟩ := hc

  by_cases hpq : ¬ (IsNontrivial p ∧ IsNontrivial q)

  by_cases hp : IsNontrivial p
  simp [hp] at hpq
  apply right_cont_boundary' at hpq
  specialize hpq x y hax hay hx hy
  contradiction
  apply right_cont_boundary at hp
  specialize hp x y hax hay hx hy
  contradiction

  apply not_not.mp at hpq
  let z : ℕ → I := nat_approach 1
  have hmz : Monotone z := nat_approach_mono
  have hz : Filter.Tendsto z Filter.atTop (nhds 1) := nat_approach_lim
  have hznone : ∀ n : ℕ, (z n) ≠ 1 := by
    intro n
    unfold z nat_approach
    apply unitInterval.lt_one_iff_ne_one.mp
    apply Subtype.mk_lt_mk.mpr
    apply max_lt_iff.mpr
    constructor
    exact Real.zero_lt_one
    simp
    exact Nat.cast_add_one_pos n

  let k : ℕ → ℕ := fun n => sSup {m : ℕ | T.npow m (z n) > p}
  let l : ℕ → ℕ := fun n => sSup {m : ℕ | T.npow m (z n) > q}

  have hmul := anti_mul_anti_anti T.toTnorm hax hay
  let a := ⨅ i, (T.mul (x i) (y i))
  apply tendsto_atTop_iInf at hmul

  have h1 : ∀ n : ℕ, T.npow ((k n) + (l n) + 2) (z n) ≤ T.mul p q := by
    intro n
    have hkln : ((k n)+(l n)+2) = (k n)+1+((l n)+1) := by ring
    calc T.npow ((k n) + (l n) + 2) (z n)
      _ = T.mul (T.npow ((k n)+1) (z n)) (T.npow ((l n)+1) (z n)) := by rw [T.npow_add, hkln]
      _ ≤ T.mul p q := by
        apply T.mul_le_mul
        exact seq_arch h hznone hpq.1.1
        exact seq_arch h hznone hpq.2.1

  have h2 : T.mul p q < a := by
    apply lt_of_le_of_ne
    swap
    by_contra ha
    rw [ha] at hc
    contradiction
    exact mul_lim_le_lim_mul T.toTnorm hax hay hx hy hmul
  have h3 : ∀ n : ℕ, a ≤ T.npow ((k n) + (l n)) (z n) := by
    intro n
    apply Metric.tendsto_atTop.mp at hx
    apply Metric.tendsto_atTop.mp at hy

    let ε := ((T.npow (k n) (z n)).1 - p) ⊓ ((T.npow (l n) (z n)).1 - q)
    have he : ε > 0 := by
      apply lt_min
      simp
      apply Nat.sSup_mem (pow_set_nonempty (z n) p hpq.1.2) (pow_set_bddAbove (z n) p (hznone n) hpq.1.1 h)
      simp
      apply Nat.sSup_mem (pow_set_nonempty (z n) q hpq.2.2) (pow_set_bddAbove (z n) q (hznone n) hpq.2.1 h)
    specialize hx ε he; specialize hy ε he
    obtain ⟨nx, hx⟩ := hx; obtain ⟨ny, hy⟩ := hy
    let n₂ := nx ⊔ ny
    specialize hx n₂ ?_; exact Nat.le_max_left nx ny
    specialize hy n₂ ?_; exact Nat.le_max_right nx ny
    have hxk : (x n₂) ≤ T.npow (k n) (z n) := by
      apply le_of_lt
      calc (x n₂).1
        _ < p+ε := by apply lt_add_of_sub_left_lt (lt_of_abs_lt hx)
        _ ≤ p+((T.npow (k n) (z n))-p) := by unfold ε; refine add_le_add ?_ ?_; rfl; apply min_le_left
        _ = (T.npow (k n) (z n)) := by ring
    have hyl : (y n₂) ≤ T.npow (l n) (z n) := by
      apply le_of_lt
      calc (y n₂).1
        _ < q+ε := by apply lt_add_of_sub_left_lt (lt_of_abs_lt hy)
        _ ≤ q+((T.npow (l n) (z n))-q) := by unfold ε; refine add_le_add ?_ ?_; rfl; apply min_le_right
        _ = (T.npow (l n) (z n)) := by ring
    calc a.1
      _ ≤ T.mul (x n₂) (y n₂) := by apply Antitone.le_of_tendsto (anti_mul_anti_anti T.toTnorm hax hay) hmul n₂
      _ ≤ T.mul (T.npow (k n) (z n)) (T.npow (l n) (z n)) := by apply T.mul_le_mul; exact hxk; exact hyl
      _ = T.npow ((k n)+(l n)) (z n) := by rw [T.npow_add]


  have hz1 : Filter.Tendsto (fun n => T.npow 2 (z n)) Filter.atTop (nhds 1) := by
    have hl := T.left_cont
    specialize hl z z 1 1 hmz hmz hz hz
    simp at hl; simp [hl]
  have hz2 : Monotone (fun n => T.npow 2 (z n)) := by
    simp
    exact mono_mul_mono_mono T.toTnorm hmz hmz
  have h4 : Filter.Tendsto (fun n => T.mul a (T.npow 2 (z n))) Filter.atTop (nhds a) := by
    have hl := T.left_cont
    specialize hl (fun n => a) (fun n => T.npow 2 (z n)) a 1 monotone_const hz2 tendsto_const_nhds hz1
    simp only [T.mul_one'] at hl
    exact hl
  have h5 : ∃ n : ℕ, T.mul p q < T.mul a (T.npow 2 (z n)) := by
    apply Metric.tendsto_atTop.mp at h4
    let ε := a-(T.mul p q).1
    have he : ε > 0 := by unfold ε; simp [h2]
    specialize h4 ε he
    obtain ⟨n, h4⟩ := h4
    specialize h4 n ?_; rfl
    use n
    calc (T.mul p q).1
      _ = a-ε := by unfold ε; ring
      _ < (T.mul a (T.npow 2 (z n))) := by exact sub_lt_of_abs_sub_lt_left h4

  obtain ⟨n, h5⟩ := h5
  have hcontra : T.npow ((k n) + (l n) + 2) (z n) < T.npow ((k n) + (l n) + 2) (z n) := by
    calc T.npow ((k n) + (l n) + 2) (z n)
      _ ≤ T.mul p q := h1 n
      _ < T.mul a (T.npow 2 (z n)) := h5
      _ ≤ T.mul (T.npow ((k n) + (l n)) (z n)) (T.npow 2 (z n)) := by apply T.mul_le_mul_right; exact h3 n
      _ = T.npow ((k n)+(l n)+2) (z n) := Tnorm.npow_add (k n + l n) 2 (z n)

  apply (lt_self_iff_false (T.npow ((k n) + (l n) + 2) (z n))).mp hcontra
