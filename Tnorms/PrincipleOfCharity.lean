import Tnorms.Defs
import Tnorms.Examples
import Tnorms.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Semicontinuous

open unitInterval




variable {T : Tnorm}
universe u
variable {X : Type u} [MetricSpace X] [hexx : Nonempty X]



noncomputable
def PC_Imp (L : FuzzyLogic T) (f : X → I) (δ : ℝ) := fun x y : X =>
  if dist x y < δ then L.imp (L.and (f x) 1) (f y) else L.imp (L.and (f x) 0) (f y)

noncomputable
def PrincipleOfCharity (L : FuzzyLogic T) (f : X → I) (δ : ℝ) :=
  sInf ( Subtype.val '' Set.range (Function.uncurry (PC_Imp L f δ)))


def PrincipleOfCharityAlmostTrue (X : Type u) [MetricSpace X] (L : FuzzyLogic T) (f : X → I) :=
  ∀ ε > 0, ∃ δ > 0, 1-ε ≤ (PrincipleOfCharity L f δ)

def IsCharitable (X : Type u) [MetricSpace X] (L : FuzzyLogic T) :=
  ∀ f : X → I, UniformContinuous f → PrincipleOfCharityAlmostTrue X L f

omit hexx in lemma pc_set_bdd {L : FuzzyLogic T} {f : X → I} {δ : ℝ} :
  BddBelow (Subtype.val '' Set.range (Function.uncurry (PC_Imp L f δ))) := by
    refine bddBelow_def.mpr ?_
    use 0
    intro y
    intro hy
    simp at hy
    obtain ⟨a, b, hab⟩ := hy
    rw [← hab]
    exact nonneg (PC_Imp L f δ a b)


lemma poc_mem (L : FuzzyLogic T) (f : X → I) (δ : ℝ) (hd : δ > 0) : (PrincipleOfCharity L f δ) ∈ I := by
  unfold PrincipleOfCharity
  simp
  constructor
  refine Real.sInf_nonneg ?_
  intro p
  intro hp
  simp at hp
  obtain ⟨a, b, hab⟩ := hp
  rw [← hab]
  exact nonneg (PC_Imp L f δ a b)

  refine csInf_le ?_ ?_
  exact pc_set_bdd

  simp
  apply Classical.choice at hexx
  use hexx
  use hexx
  unfold PC_Imp
  refine SetCoe.ext ?_
  simp [hd, L.and_def, FuzzyLogic.imp_self]




omit [Nonempty X] in lemma inst_poc (L : FuzzyLogic T) (f : X → I) (δ : ℝ) (x y : X) (hxy : dist x y < δ) :
  PrincipleOfCharity L f δ ≤ L.imp (f x) (f y) := by
    unfold PrincipleOfCharity
    refine csInf_le ?_ ?_
    exact pc_set_bdd

    simp
    use x
    use y
    unfold PC_Imp
    simp [hxy, L.and_def, T.mul_one]

-- Proposition 1
theorem poc_dec (f : X → I) (L : FuzzyLogic T) {δ δ' : ℝ} :
  0 < δ' → δ' ≤ δ → (PrincipleOfCharity L f δ) ≤ (PrincipleOfCharity L f δ') := by
    intro d
    intro h

    conv => rhs
            unfold PrincipleOfCharity

    refine le_csInf ?_ ?_
    refine Set.Nonempty.image Subtype.val ?_
    exact Set.range_nonempty (Function.uncurry (PC_Imp L f δ'))


    intro p
    intro hp
    simp at hp

    obtain ⟨x, y, hxy⟩ := hp
    unfold PC_Imp at hxy

    by_cases hd : dist x y < δ'

    simp [hd, L.and_def] at hxy
    apply lt_of_lt_of_le hd at h
    calc PrincipleOfCharity L f δ
      _ ≤ L.imp (f x) (f y) := by exact inst_poc L f δ x y h
      _ = p := by exact hxy

    simp [hd, L.and_def, FuzzyLogic.imp_zero] at hxy
    rw [← hxy]
    apply lt_of_lt_of_le d at h
    exact (poc_mem L f δ h).2



omit [Nonempty X] in lemma poc_diff_ep {ε : ℝ} {f : X → I}{δ : ℝ}{x y : X}(he: ε > 0) (hxy: dist x y < δ)
  (h : 1-ε/2 ≤ PrincipleOfCharity Tnorm.LukFuzzy f δ) : (f x) - (f y) < ε := by
    have h2 : 1 - ε < 1 - (f x) + (f y) := by
      calc 1 - ε
        _ < 1 - ε/2 := by linarith
        _ ≤ PrincipleOfCharity Tnorm.LukFuzzy f δ := by exact h
        _ ≤ Tnorm.LukFuzzy.imp (f x) (f y) := by exact inst_poc Tnorm.LukFuzzy f δ x y hxy
        _ = min 1 (1 - (f x).1 + (f y)) := by rw[Tnorm.luk_imp_min]
        _ ≤ 1 - (f x) + (f y) := by simp

    linarith [h2]


-- Theorem 2
theorem pocat_iff_uni_cont (f : X → I) :
  (UniformContinuous f) ↔ (PrincipleOfCharityAlmostTrue X Tnorm.LukFuzzy f) := by
  constructor

  -- forward direction
  intro h
  unfold PrincipleOfCharityAlmostTrue
  intro ε
  intro he

  apply Metric.uniformContinuous_iff.mp at h
  specialize h ε he
  obtain ⟨δ, hd⟩ := h
  obtain ⟨hd, hc⟩ := hd

  use δ
  constructor
  exact hd

  unfold PrincipleOfCharity
  refine le_csInf ?_ ?_
  simp
  exact Set.range_nonempty (Function.uncurry (PC_Imp Tnorm.LukFuzzy f δ))

  intro p
  intro hp
  simp at hp

  obtain ⟨x, y, hxy⟩ := hp
  unfold PC_Imp at hxy

  by_cases hdist : dist x y < δ

  specialize hc hdist
  simp [hdist, Tnorm.LukFuzzy.and_def, Tnorm.luk_imp_min] at hxy
  rw [← hxy]
  simp

  constructor
  exact le_of_lt he
  calc 1
    _ = 1+ε-ε := by simp
    _ ≤ 1+ε-(|(f x) - (f y).1|) := by refine sub_le_sub_left ?_ (1+ε); exact le_of_lt hc
    _ ≤ 1+ε-((f x) - (f y).1) := by refine sub_le_sub_left ?_ (1+ε); exact le_abs_self ((f x) - (f y).1)
    _ = 1-(f x).1 + (f y)+ε := by ring

  simp [hdist, Tnorm.LukFuzzy.and_def, Tnorm.luk_imp_min] at hxy

  calc 1-ε
    _ ≤ 1 := by simp; exact le_of_lt he
    _ = min 1 (1+ (f y).1) := by refine eq_min ?_ ?_ fun {d} a a_1 ↦ a; rfl; simp; exact nonneg (f y)
    _ ≤ p := by exact le_of_eq hxy



  -- backward direction
  intro h
  refine Metric.uniformContinuous_iff.mpr ?_

  intro ε
  intro he

  have he2 : ε/2 > 0 := by simp [he]

  apply h at he2
  obtain ⟨δ, hd⟩ := he2

  use δ
  obtain ⟨delp, hpoc⟩ := hd

  simp [delp]

  intro x y
  intro hxy

  refine abs_sub_lt_iff.mpr ?_
  constructor
  exact poc_diff_ep he hxy hpoc
  have hyx : dist y x < δ := by exact Metric.mem_ball'.mp hxy
  exact poc_diff_ep he hyx hpoc


theorem luk_is_charitable : IsCharitable X Tnorm.LukFuzzy := by
  intro f
  intro h
  exact (pocat_iff_uni_cont f).mp h



def LowerSemicontinuousTnorm (T : Tnorm) := ∀ p₀ q₀ : I, ∀ ε > 0, ∃ δ > 0, ∀ p q : I,
  p₀.1-δ < p → p ≤ p₀ → q₀.1 - δ < q → q ≤ q₀ → (T.mul p₀ q₀) - (T.mul p q).1 < ε
def IsLeftContinuousTnorm (T : Tnorm) := ∀ p q : I, ∀ ε > 0, ∃ δ > 0,
  ∀ r : I, p.1-δ < r → r ≤ p → |(T.mul r q).1 - (T.mul p q)| < ε

-- Proposition 4
-- The converse is also true
-- I should move this to the LeftContinuousTnorm section when done
theorem left_cont_iff_lower_semicont_tnorm (T : Tnorm) : IsLeftContinuousTnorm T ↔ LowerSemicontinuousTnorm T := by
    constructor
    intro h
    intro p₀ q₀
    intro ε
    intro he
    apply half_pos at he
    have he2 : ε/2 > 0 := by exact he

    apply h p₀ q₀ at he
    obtain ⟨δ₁, hd1⟩ := he
    obtain ⟨hd1p, hd1⟩ := hd1
    let p₁ : I := ⟨max 0 (p₀-(δ₁/2)), FuzzyLogic.max_del_mem hd1p⟩

    apply h q₀ p₁ at he2
    obtain ⟨δ₂, hd2⟩ := he2
    obtain ⟨hd2p, hd2⟩ := hd2
    let q₁ : I := ⟨max 0 (q₀-(δ₂/2)), FuzzyLogic.max_del_mem hd2p⟩

    let δ := min (δ₁/2) (δ₂/2)
    use δ
    constructor
    apply half_pos at hd1p
    apply half_pos at hd2p
    exact lt_min hd1p hd2p

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
        simp [hd1p]
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
      rw [← abs_neg] at hd1
      simp at hd1
      nth_rw 1 [T.mul_comm] at hd2
      nth_rw 2 [T.mul_comm] at hd2
      rw [← abs_neg] at hd2
      simp at hd2

      calc |(T.mul p₀ q₀).1 - (T.mul p₁ q₁)|
        _ ≤ |(T.mul p₀ q₀).1 - (T.mul p₁ q₀)|+|(T.mul p₁ q₀).1-(T.mul p₁ q₁)| := by exact abs_sub_le (T.mul p₀ q₀).1 (T.mul p₁ q₀) (T.mul p₁ q₁)
        _ < ε/2 + |(T.mul p₁ q₀).1-(T.mul p₁ q₁)| := by exact (add_lt_add_iff_right |(T.mul p₁ q₀).1 - (T.mul p₁ q₁)|).mpr hd1
        _ < ε/2 + ε/2 := by exact (add_lt_add_iff_left (ε/2)).mpr hd2
        _ = ε := by simp

    calc (T.mul p₀ q₀).1 - (T.mul p q)
      _ ≤ (T.mul p₀ q₀).1 - (T.mul p₁ q₁) := by exact tsub_le_tsub_left hmul ↑(T.mul p₀ q₀)
      _ ≤ |(T.mul p₀ q₀).1 - (T.mul p₁ q₁)| := by exact le_abs_self ((T.mul p₀ q₀).1 - (T.mul p₁ q₁))
      _ < ε := by exact hin



    intro h
    intro p q ε he
    specialize h p q ε he
    obtain ⟨δ, hdp, hmul⟩ := h
    use δ
    constructor
    exact hdp
    intro r hrl hrg
    rw [abs_eq_max_neg]
    apply max_lt

    apply T.mul_le_mul_right r p at hrg
    specialize hrg q
    apply sub_lt_iff_lt_add.mpr
    calc (T.mul r q).1
      _ ≤ (T.mul p q) := by exact hrg
      _ < ε+(T.mul p q) := by exact lt_add_of_pos_left (↑(T.mul p q)) he

    simp
    specialize hmul r q hrl hrg ?_ ?_
    simp [hdp]
    rfl
    exact hmul
/-
The definition of lower semicontinuous that is given in my paper (and in the Triangular Norms book)
  is different from the typical definition.  However, they are equivalent for Tnorms, as we
  demonstrate here.
-/
theorem lower_semicont_tnorm_is_lower_semicont : LowerSemicontinuousTnorm T ↔ LowerSemicontinuous T.mul.uncurry := by
  /-unfold LowerSemicontinuous
  intro pq
  unfold LowerSemicontinuousAt
  intro t
  intro ht
  refine Metric.eventually_nhds_iff.mpr ?_-/

  /-let ε := (T.mul pq.1 pq.2).1-t
  have he : ε > 0 := by exact sub_pos.mpr ht
  have he2 : ε > 0 := by exact he
  apply T.left_cont_x at he
  obtain ⟨δ, hd⟩ := he
  obtain ⟨hdp, hd⟩ := hd
  use δ
  constructor
  exact_mod_cast hdp
  intro xy-/

  sorry


variable {T : LeftContinuousTnorm}

-- Lemma 5
lemma uni_cont_ish_boundary (T : LeftContinuousTnorm) : ∀ ε > 0, ∃ δ > 0, ∀ p q : I,
  1-q.1 < δ → p.1-(T.mul p q) < ε := by

    intro ε he

    have hp : ∀ p : I, ∃ γ > 0, γ ≤ ε/2 ∧
      (∀ q r : I, |r-p.1| < γ → 1 - q < γ → p.1-(T.mul r q) < ε/2) := by
        intro p
        have he2 : ε/2 > 0 := by exact half_pos he
        have hLSCT : LowerSemicontinuousTnorm T.toTnorm := by apply (left_cont_iff_lower_semicont_tnorm T.toTnorm).mp; exact T.left_cont_x
        apply hLSCT p 1 at he2
        obtain ⟨δ, hdp, hd⟩ := he2
        use min δ (ε/2)
        constructor
        simp [hdp, he]
        constructor
        simp
        intro q r h hq

        have hq : 1-δ < q := by
          apply lt_min_iff.mp at hq
          apply And.left at hq
          exact sub_lt_comm.mp hq

        by_cases hr : r ≤ p

        specialize hd r q ?_ hr ?_ ?_
        apply lt_min_iff.mp at h
        apply And.left at h
        rw [abs_eq_max_neg] at h
        apply max_lt_iff.mp at h
        apply And.right at h
        simp at h
        exact sub_lt_comm.mp h

        exact hq
        exact le_one q

        simp at hd
        exact hd

        apply lt_of_not_ge at hr
        apply le_of_lt at hr
        calc p.1 - (T.mul r q)
          _ ≤ p - (T.mul p q) := by refine tsub_le_tsub ?_ ?_; rfl; exact T.mul_le_mul_right p r hr q
          _ < ε/2 := by specialize hd p q ?_ ?_ hq (le_one q); simp [hdp]; rfl; simp at hd; exact hd

    choose G hg using hp
    let U : I → Set ℝ := fun p => Set.Ioo (p.1 - (G p)) (p.1 + (G p))

    have hi : IsCompact I := by exact isCompact_Icc
    apply IsCompact.elim_finite_subcover at hi
    specialize hi U ?_ ?_
    intro p
    exact isOpen_Ioo

    intro p hp
    simp
    use p
    use hp
    unfold U
    simp
    specialize hg ⟨p, hp⟩
    exact hg.left

    obtain ⟨t, ht⟩ := hi
    let tg := Finset.image G t
    have hnet : tg.Nonempty := by
      refine Finset.image_nonempty.mpr ?_
      apply Set.mem_of_subset_of_mem at ht
      specialize ht zero_mem
      simp at ht
      obtain ⟨i, hi, hit, hiU⟩ := ht
      use ⟨i, hi⟩
    let δ := Finset.min' tg hnet

    use δ
    constructor
    refine (Finset.lt_min'_iff tg hnet).mpr ?_
    intro y hy
    unfold tg at hy
    simp at hy
    obtain ⟨a, haI, hat, haG⟩ := hy
    rw [← haG]
    specialize hg ⟨a, haI⟩
    exact hg.left

    intro p q hq
    apply Set.mem_of_subset_of_mem at ht
    specialize ht p.2
    simp at ht
    obtain ⟨i, hi, hit, hiU⟩ := ht
    unfold U at hiU
    simp at hiU

    have hq : 1-q < G ⟨i, hi⟩ := by
      calc 1-q.1
        _ < δ := by exact hq
        _ ≤ G ⟨i, hi⟩ := by refine Finset.min'_le tg (G ⟨i, hi⟩) ?_; unfold tg; simp; use i; use hi
    have hpi : |p-i| < G ⟨i, hi⟩ := by
      rw [abs_eq_max_neg]
      apply max_lt
      exact sub_left_lt_of_lt_add hiU.right
      simp
      exact sub_lt_comm.mp hiU.left
    specialize hg ⟨i, hi⟩
    have hpie : p-i < ε/2 := by
      calc p-i
        _ ≤ |p-i| := by exact le_abs_self (↑p - i)
        _ < G ⟨i, hi⟩ := by exact hpi
        _ ≤ ε/2 := by exact hg.right.left
    apply And.right at hg
    apply And.right at hg
    specialize hg q p hpi hq
    calc p.1-(T.mul p q)
      _ < (i+(ε/2))-(T.mul p q).1 := by refine sub_lt_sub_right ?_ (T.mul p q).1; exact lt_add_of_tsub_lt_left hpie
      _ = i-(T.mul p q)+(ε/2) := by ring
      _ < (ε/2)+(ε/2) := by exact (add_lt_add_iff_right (ε / 2)).mpr hg
      _ = ε := by ring


-- Theorem 8
-- We will likely need to prove some facts about T-norm ismorphisms before proving this
theorem charitable_is_iso_invariant (T₁ T₂ : Tnorm) (L₁ : FuzzyLogic T₁) (L₂ : FuzzyLogic T₂) :
  (∃ φ : I → I, Tnorm.IsIsomorphismBetween T₁ T₂ φ) → IsCharitable X L₁ → IsCharitable X L₂ := by
    sorry


-- Corollary 9
-- This will require a major structure theorem about T-norms
theorem charitable_of_nilpotent (L : FuzzyLogic T.toTnorm) : IsNilpotent T.toTnorm → IsCharitable X L := by
  sorry


/-
The three main theorems from my paper.  In the paper they are stated as one theorem (Theorem 3),
  but here we state each of the three directions separately. One could combine these in various
  ways, but this only makes sense if I anticipate the theorems being used (which I don't).

The proof strategy is being developed above
-/

omit hexx in theorem uni_cont_of_pocat (L : FuzzyLogic T.toTnorm) (f : X → I) :
  PrincipleOfCharityAlmostTrue X L f → UniformContinuous f := by

    intro h
    apply Metric.uniformContinuous_iff.mpr

    intro ε
    intro he
    apply uni_cont_ish_boundary T ε at he
    obtain ⟨δ', hdp', hd'⟩ := he
    have hdp'2 : δ' > 0 := by exact hdp'
    apply half_pos at hdp'

    specialize h (δ'/2) hdp'
    obtain ⟨δ, hdp, hd⟩ := h
    use δ
    constructor
    exact hdp
    intro x y hxy
    have hyx : dist y x < δ := by exact Metric.mem_ball'.mp hxy

    refine abs_sub_lt_iff.mpr ?_
    constructor


    have hd : 1-(δ'/2) ≤ L.imp (f x) (f y) := by
      calc 1-(δ'/2)
        _ ≤ PrincipleOfCharity L f δ := by exact hd
        _ ≤ L.imp (f x) (f y) := by exact inst_poc L f δ x y hxy
    have himp : 1-(L.imp (f x) (f y)).1 < δ' := by
      calc 1-(L.imp (f x) (f y)).1
        _ ≤ δ'/2 := by exact tsub_le_iff_tsub_le.mp hd
        _ < δ' := by refine half_lt_self ?_; exact hdp'2

    calc (f x).1 - (f y)
      _ ≤ (f x).1 - (T.mul (f x) (L.imp (f x) (f y))) := by refine tsub_le_tsub ?_ ?_; rfl; exact FuzzyLogic.and_imp (f x) (f y)
      _ < ε := by apply hd' (f x) (L.imp (f x) (f y)); exact himp


    have hd : 1-(δ'/2) ≤ L.imp (f y) (f x) := by
      calc 1-(δ'/2)
        _ ≤ PrincipleOfCharity L f δ := by exact hd
        _ ≤ L.imp (f y) (f x) := by exact inst_poc L f δ y x hyx
    have himp : 1-(L.imp (f y) (f x)).1 < δ' := by
      calc 1-(L.imp (f y) (f x)).1
        _ ≤ δ'/2 := by exact tsub_le_iff_tsub_le.mp hd
        _ < δ' := by refine half_lt_self ?_; exact hdp'2

    calc (f y).1 - (f x)
      _ ≤ (f y).1 - (T.mul (f y) (L.imp (f y) (f x))) := by refine tsub_le_tsub ?_ ?_; rfl; exact FuzzyLogic.and_imp (f y) (f x)
      _ < ε := by apply hd' (f y) (L.imp (f y) (f x)); exact himp


theorem charitable_of_luk (L : FuzzyLogic T.toTnorm) :
  (∃ φ : I → I, Tnorm.IsIsomorphismBetween Tnorm.LukTnorm T.toTnorm φ) → IsCharitable X L := by
    intro h
    apply charitable_is_iso_invariant at h
    apply h
    exact luk_is_charitable
    exact hexx



/- A question here is can we remove the for all from the implication?
  That is, we have shown that if L is charitable for all X, L must be Luk
  (In particular, if L is charitable for [0,1], then L must be Luk).
  However, is it true that if L is charitable for some X, then L must be Luk?
  We do know that if there is an X such that L is not charitable for X, then L
  must be not charitable for [0,1].  But the other question is more subtle and
  seems like it could be hard to answer
-/
theorem luk_of_I_charitable (L : FuzzyLogic T.toTnorm) :
  IsCharitable I L → (∃ φ : I → I, Tnorm.IsIsomorphismBetween Tnorm.LukTnorm T.toTnorm φ) := by
    sorry
