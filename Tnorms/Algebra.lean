import Tnorms.Defs
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

def IsStrictlyMonotone := ∀ p : I, p > 0 → ∀ q r : I, q < r → T.mul p q < T.mul p r

def IsCancellative := ∀ p q r : I, T.mul p q = T.mul p r → (p = 0 ∨ q = r)

def IsConditionalCancellative := ∀ p q r : I, T.mul p q = T.mul p r → T.mul p r > 0 → q = r

def IsArchimedean := ∀ p q : I, IsNontrivial p → IsNontrivial q → ∃ n : ℕ,
  T.npow n p < q


lemma cond_canc_of_canc : IsCancellative T → IsConditionalCancellative T := by
  intro h
  intro p q r
  intro h2
  intro h3
  apply h at h2

  obtain h0|heq := h2

  rw [h0] at h3
  simp at h3

  exact heq


lemma canc_iff_strictly_mono : IsCancellative T ↔ IsStrictlyMonotone T := by
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


lemma nntid_of_strictly_mono : IsStrictlyMonotone T → ¬ HasNontrivialIdempotent T := by
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

lemma nzd_of_strictly_mono : IsStrictlyMonotone T → ¬ HasZeroDivisors T := by
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

lemma nzd_of_canc : IsCancellative T → ¬ HasZeroDivisors T := by
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


def IsStrict := Continuous T.mul ∧ IsStrictlyMonotone T

def IsNilpotent := Continuous T.mul ∧ ∀ p : I, IsNontrivial p → ∃ n : ℕ,
  T.npow n p = 0


/-lemma arch_of_strict : IsStrict T → IsArchimedean T := by
  sorry-/

/-lemma cond_canc_of_nilpt : IsNilpotent T → IsConditionalCancellative T := by
  sorry-/

lemma arch_of_nilpt : IsNilpotent T → IsArchimedean T := by
  intro h
  intro p q hpnt hqnt
  apply And.right at h
  specialize h p hpnt
  obtain ⟨n, hn⟩ := h
  use n
  calc T.npow n p
    _ = 0 := by exact hn
    _ < q := by apply unitInterval.pos_iff_ne_zero.mpr hqnt.left

lemma nntid_of_nilpt : IsNilpotent T → ¬ HasNontrivialIdempotent T := by
  intro h
  apply arch_of_nilpt at h
  apply nntid_of_arch at h
  exact h

/-lemma arch_of_cont_nntid : ¬ HasNontrivialIdempotent T → Continuous T.mul → IsArchimedean T := by
  intro h hc
  by_contra ha
  unfold HasNontrivialIdempotent at h; unfold IsArchimedean at ha
  push_neg at h; push_neg at ha
-/

noncomputable
def rightLim (T : Tnorm) (p q : I) := sInf (Subtype.val '' ((Function.uncurry T.mul) '' {(r, s) : I × I | (p ≤ r ∧ q < s) ∨ (p < r ∧ q ≤ s)}))
lemma rightLimI {T : Tnorm} {p q : I} : rightLim T p q ∈ I := by sorry

noncomputable
def leftLim (T : Tnorm) (p q : I) := sInf (Subtype.val '' ((Function.uncurry T.mul) '' {(r, s) : I × I | (s ≤ p ∧ s < q) ∨ (r < p ∧ s ≤ q)}))
lemma leftLimI {T : Tnorm} {p q : I} : leftLim T p q ∈ I := by sorry

theorem right_cont_lim {T : Tnorm} (h : ∀ p q : I, rightLim T p q = T.mul p q) : IsRightContinuousTnorm T := by
  sorry

theorem left_cont_lim {T : Tnorm} (h : ∀ p q : I, leftLim T p q = T.mul p q) : IsLeftContinuousTnorm T := by
  sorry

theorem cont_of_left_right_cont {T : Tnorm} : IsLeftContinuousTnorm T → IsRightContinuousTnorm T → Continuous T.mul := by
  sorry

theorem right_cont_on_boundary (T : Tnorm) (p q : I) : (¬ IsNontrivial p ∨ ¬ IsNontrivial q) →
  rightLim T p q = T.mul p q := by
    sorry

theorem le_right_lim (T : Tnorm) (p q : I) : T.mul p q ≤ rightLim T p q := by
    sorry

theorem min_pow_arch (T : Tnorm) (h : IsArchimedean T) : ∀ p q : I, IsNontrivial p → IsNontrivial q →
  ∃ n : ℕ, T.npow (n+1) p ≤ q ∧ q < T.npow n p := by
    sorry

noncomputable
def limI (z : ℕ → I) (hz : ∀ n : ℕ, z n ≤ z (n+1)) := sSup (Subtype.val '' (Set.range z))
--theorem seq_T_inc (T : Tnorm) (z : ℕ → I)
--theorem left_cont_seq_lim (T : Tnorm) (z : ℕ → I) (hz : ∀ n : ℕ, z n ≤ z (n+1)) :

theorem cont_of_left_cont_arch (T : LeftContinuousTnorm) : IsArchimedean T.toTnorm → Continuous T.mul := by
  intro h
  apply cont_of_left_right_cont
  exact left_cont_is_left_cont T
  apply right_cont_lim
  intro x y
  by_cases hnt : (¬ IsNontrivial x ∨ ¬ IsNontrivial y)
  exact right_cont_on_boundary T.toTnorm x y hnt

  push_neg at hnt
  by_contra hc
  push_neg at hc
  symm at hc
  apply lt_of_le_of_ne (le_right_lim T.toTnorm x y) at hc

  let z : ℕ → I := fun n => ⟨1-1/(n+2), by
      constructor
      simp
      refine inv_le_one_of_one_le₀ ?_
      linarith

      simp
      linarith
    ⟩
  have hznt : ∀ n : ℕ, IsNontrivial (z n) := by sorry
  let u : ℕ → ℕ := fun n => Classical.choose (min_pow_arch T.toTnorm h (z n) x (hznt n) hnt.1)
  let v : ℕ → ℕ := fun n => Classical.choose (min_pow_arch T.toTnorm h (z n) y (hznt n) hnt.2)

  have hnn2 : ∀ n : ℕ, T.npow ((u n) + (v n) + 2) (z n) ≤ T.mul x y := by sorry
  have hnn : ∀ n : ℕ, rightLim T.toTnorm x y ≤ T.npow ((u n) + (v n)) (z n) := by
      sorry

  have hnn22 : ∀ n : ℕ, T.mul (⟨rightLim T.toTnorm x y, rightLimI⟩) (T.mul (z n) (z n)) ≤  T.npow ((u n) + (v n) + 2) (z n) := by
      sorry


  sorry
