import Tnorms.Defs
import Tnorms.FuzzyLogic
import Tnorms.Examples
import Tnorms.Basic
import Tnorms.Algebra
import Tnorms.Isomorphism
import Tnorms.LeftContinuity
import Tnorms.Continuity
import Tnorms.LeftContinuousArchimedean
import Tnorms.Structure

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.UniformSpace.HeineCantor
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
  obtain ⟨δ, hd⟩ := h (ε/2) (half_pos he)
  use δ
  obtain ⟨hd, hpoc⟩ := hd

  constructor
  exact hd
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



variable {T : LeftContinuousTnorm}

-- Lemma 5
lemma uni_cont_ish_boundary (T : LeftContinuousTnorm) : ∀ ε > 0, ∃ δ > 0, ∀ p q : I,
  1-q.1 < δ → p.1-(T.mul p q) < ε := by

    intro ε he

    have hp : ∀ p : I, ∃ γ > 0, γ ≤ ε/2 ∧
      (∀ q r : I, |r-p.1| < γ → 1 - q < γ → p.1-(T.mul r q) < ε/2) := by
        intro p
        let he2 := half_pos he
        apply ((left_cont_lower_semi T.toTnorm).mp T.left_cont) p 1 at he2
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
        apply sub_lt_comm.mp hd

        apply lt_of_not_ge at hr
        apply le_of_lt at hr
        calc p.1 - (T.mul r q)
          _ ≤ p - (T.mul p q) := by refine tsub_le_tsub ?_ ?_; rfl; exact T.mul_le_mul_right p r hr q
          _ < ε/2 := by specialize hd p q ?_ ?_ hq (le_one q); simp [hdp]; rfl; simp at hd; apply sub_lt_comm.mp hd

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
-- We will likely need to prove some facts about T-norm isomorphisms before proving this
theorem charitable_is_iso_invariant (T₁ T₂ : LeftContinuousTnorm) (L₁ : FuzzyLogic T₁.toTnorm) (L₂ : FuzzyLogic T₂.toTnorm) :
  Tnorm.Isomorphic T₁.toTnorm T₂.toTnorm → IsCharitable X L₁ → IsCharitable X L₂ := by
    intro hi h
    obtain ⟨φ, hi⟩ := hi
    intro f hf
    let φ' := Function.invFun φ
    let g : X → I := φ' ∘ f
    have hug : UniformContinuous g := by
      apply UniformContinuous.comp
      apply uni_cont_of_iso
      apply Tnorm.iso_inv_is_iso
      exact hi.left
      exact hf
    have hφ : Function.RightInverse φ' φ := by
      apply Function.rightInverse_invFun
      exact hi.1.1.2
    have hfg : f = φ ∘ g := by unfold g; rw [← Function.comp_assoc, Function.RightInverse.id hφ]; rfl


    intro ε he
    by_cases heh : ε > 1
    use 1
    simp
    calc 1
      _ ≤ (PrincipleOfCharity L₂ f 1)+1 := by refine tsub_le_iff_right.mp ?_; simp; exact (poc_mem L₂ f 1 one_pos).left
      _ ≤ (PrincipleOfCharity L₂ f 1)+ε := by refine add_le_add_left ?_ (PrincipleOfCharity L₂ f 1); exact le_of_lt heh

    have heI : ε ∈ I := by
      apply Set.mem_Icc.mpr
      constructor
      exact le_of_lt he
      exact le_of_not_gt heh
    have hφ2 : φ (φ' (σ ⟨ε, heI⟩)) = σ ⟨ε, heI⟩ := by exact hφ (σ ⟨ε, heI⟩)
    specialize h g hug (1- (φ' (σ ⟨ε, heI⟩))) ?_
    simp
    apply unitInterval.lt_one_iff_ne_one.mpr
    apply_fun φ
    rw [Tnorm.iso_one φ hi.left]
    rw [hφ2]
    apply_fun σ
    rw [symm_symm, symm_one]
    apply unitInterval.pos_iff_ne_zero.mp
    exact he


    obtain ⟨δ, hdp, hd⟩ := h
    use δ
    constructor
    exact hdp
    simp at hd

    unfold PrincipleOfCharity
    apply le_csInf
    apply Set.image_nonempty.mpr
    apply Set.range_nonempty

    intro b hb
    simp at hb
    unfold PC_Imp at hb
    obtain ⟨x, y, hb⟩ := hb
    by_cases hxy : dist x y < δ
    simp [hxy, FuzzyLogic.and_def] at hb
    unfold PrincipleOfCharity at hd
    have hsnone : (Subtype.val '' Set.range (Function.uncurry (PC_Imp L₁ g δ))).Nonempty := by exact Set.Nonempty.of_subtype
    apply (le_csInf_iff pc_set_bdd hsnone).mp at hd

    let p : I := L₁.imp (g x) (g y)
    specialize hd p ?_
    simp
    use x
    use y
    unfold PC_Imp
    simp [hxy, FuzzyLogic.and_def]
    rfl

    unfold p at hd
    have hd : T₁.mul (φ' (σ ⟨ε, heI⟩)) (g x) ≤ (g y) := by
      exact (FuzzyLogic.le_imp_iff_and_le L₁ (g x) (g y) (φ' (σ ⟨ε, heI⟩))).mpr hd
    have hbb : T₂.mul (σ ⟨ε, heI⟩) (f x) ≤ (f y) := by
      calc T₂.mul (σ ⟨ε, heI⟩) (f x)
        _ = T₂.mul (σ ⟨ε, heI⟩) (φ (g x)) := by rw [hfg]; rfl
        _ = T₂.mul (φ (φ' (σ ⟨ε, heI⟩))) (φ (g x)) := by rw [hφ2]
        _ = φ (T₁.mul (φ' (σ ⟨ε, heI⟩)) (g x)) := by rw [← hi.right]
        _ ≤ φ (g y) := by apply hi.left.right; exact hd
        _ = f y := by rw [hfg]; rfl
    apply (FuzzyLogic.le_imp_iff_and_le L₂ (f x) (f y) (σ ⟨ε, heI⟩)).mp at hbb
    rw [← hb]
    exact hbb

    simp [hxy, FuzzyLogic.and_def] at hb
    rw [← hb]
    simp
    exact le_of_lt he



-- Theorem 6
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
  Tnorm.Isomorphic Tnorm.LukTnorm.toTnorm T.toTnorm → IsCharitable X L := by
    intro h
    apply charitable_is_iso_invariant at h
    apply h
    exact luk_is_charitable
    exact hexx

-- Corollary 9
-- This requires a major structure theorem about T-norms
theorem charitable_of_nilpotent (L : FuzzyLogic T.toTnorm) : Nilpotent T.toTnorm → IsCharitable X L := by
  intro h
  apply luk_iso_of_nilpt at h
  apply charitable_of_luk at h
  exact h
  exact hexx


lemma pocat_for_id (L : FuzzyLogic T.toTnorm) (h : ∃ ε : I, (ε > 0) ∧ (∀ δ > 0, ∃ x y : I, dist x y < δ ∧ (T.mul (σ ε) x) > y)) :
  ¬ PrincipleOfCharityAlmostTrue I L id := by
    unfold PrincipleOfCharityAlmostTrue PrincipleOfCharity PC_Imp
    simp
    obtain ⟨ε, hep, h⟩ := h
    use ε
    constructor
    exact hep
    intro δ hdp
    specialize h δ hdp
    obtain ⟨x, y, hxy, hmul⟩ := h
    refine lt_tsub_iff_right.mp ?_
    refine (csInf_lt_iff pc_set_bdd ?_).mpr ?_

    use (1 : I)
    simp
    use 0
    simp
    use 0
    unfold PC_Imp
    simp [hdp, L.and_def]
    refine Set.Icc.coe_eq_one.mp ?_
    exact L.imp_zero 0

    use L.imp x y
    constructor
    simp
    constructor
    constructor
    exact nonneg (L.imp x y)
    exact le_one (L.imp x y)
    use x
    use x.2
    use y
    use y.2
    unfold PC_Imp
    simp [hxy, L.and_def]

    apply lt_of_not_le
    apply (L.le_imp_iff_and_le x y (σ ε)).not.mp
    apply not_le_of_lt
    exact hmul


lemma left_tnorm_cases (T : LeftContinuousTnorm) :
  Nilpotent T.toTnorm ∨
  ¬ HasZeroDivisors T.toTnorm ∨
  HasNontrivialIdempotent T.toTnorm ∨
  (¬ IsArchimedean T.toTnorm ∧ ¬ HasNontrivialIdempotent T.toTnorm) := by
    by_cases h : HasNontrivialIdempotent T.toTnorm
    right; right; left; exact h

    by_cases h2 : ¬HasZeroDivisors T.toTnorm
    right; left; exact h2
    rw [not_not] at h2

    by_cases h3: ¬IsArchimedean T.toTnorm
    right; right; right;
    constructor; exact h3; exact h

    rw [not_not] at h3
    left
    have hc : T.Continuous := by exact cont_of_left_cont_arch T h3
    apply nilpt_of_cont_arch_zd T.toTnorm hc h3 h2

/- A question here is can we remove the for all from the implication?
  That is, we have shown that if L is charitable for all X, L must be Luk
  (In particular, if L is charitable for [0,1], then L must be Luk).
  However, is it true that if L is charitable for some X, then L must be Luk?
  We do know that if there is an X such that L is not charitable for X, then L
  must be not charitable for [0,1].  But the other question is more subtle and
  seems like it could be hard to answer
-/

theorem not_charitable_of_nzds (T : Tnorm) : ¬ HasZeroDivisors T →
  ∃ ε > 0, ∀ δ > 0, ∃ x y, dist x y < δ ∧ T.mul (σ ε) x > y := by
    intro h
    let ε : I := ⟨1/2, half_mem_I⟩
    have he0 : ε ≠ 0 := half_nontrivial.1
    have he1 : ε ≠ 1 := half_nontrivial.2

    use ε
    constructor
    apply unitInterval.pos_iff_ne_zero.mpr he0

    intro δ hdp
    by_cases hd : δ/2 > 1

    use 1
    use 0
    constructor
    calc |1-0|
      _ = (1:ℝ) := by simp
      _ < δ := by linarith
    rw [T.mul_one']
    refine unitInterval.pos_iff_ne_zero.mpr ?_
    apply_fun σ
    rw [symm_symm, symm_zero]
    exact he1

    have hdI : δ/2 ∈ I := by
      constructor
      apply le_of_lt; exact half_pos hdp
      linarith
    use ⟨δ/2, hdI⟩
    use 0
    constructor
    calc |(δ/2)-0|
      _ = δ/2 := by simp; apply le_of_lt; exact half_pos hdp
      _ < δ := by simp [hdp]

    unfold HasZeroDivisors at h
    simp at h
    specialize h (σ ε) (σ ε).2
    refine unitInterval.pos_iff_ne_zero.mpr ?_
    apply h

    apply_fun σ
    rw [symm_symm, symm_zero]
    exact he1

    refine unitInterval.pos_iff_ne_zero.mp ?_
    exact half_pos hdp
    exact hdI

theorem not_charitable_of_ntid (T : Tnorm) : HasNontrivialIdempotent T →
  ∃ ε > 0, ∀ δ > 0, ∃ x y, dist x y < δ ∧ T.mul (σ ε) x > y := by
    intro h
    obtain ⟨e, hent, hem⟩ := h
    use σ e
    constructor
    apply unitInterval.pos_iff_ne_zero.mpr
    apply_fun σ
    rw [symm_symm, symm_zero]
    exact hent.right

    intro δ hdp
    use e
    let y : I := ⟨max 0 (e-(δ/2)), by
      constructor
      simp
      simp
      calc e.1
        _ ≤ 1 := by exact le_one e
        _ ≤ 1+(δ/2) := by simp; apply le_of_lt; exact half_pos hdp
    ⟩
    use y
    have hey : y.1 < e := by
      apply max_lt_iff.mpr
      constructor
      exact unitInterval.pos_iff_ne_zero.mpr hent.left
      simp [hdp]
    constructor
    refine max_lt ?_ ?_
    calc e-y.1
      _ ≤ e-(e-(δ/2)) := by refine sub_le_sub ?_ ?_; rfl; exact le_max_right 0 (↑e - δ / 2)
      _ = δ/2 := by ring
      _ < δ := by exact div_two_lt_of_pos hdp
    calc -(e-y.1)
      _ = y-e := by ring
      _ < 0 := by exact sub_neg.mpr hey
      _ < δ := by exact hdp

    rw [symm_symm, hem]
    exact hey

theorem not_charitable_of_nonarch_nntid (T : Tnorm) : ¬ IsArchimedean T ∧ ¬ HasNontrivialIdempotent T →
  ∃ ε > 0, ∀ δ > 0, ∃ x y, dist x y < δ ∧ T.mul (σ ε) x > y := by
    intro h
    obtain ⟨h1, h2⟩ := h
    unfold IsArchimedean at h1
    push_neg at h1
    obtain ⟨p, q, hpnt, hqnt, hpq⟩ := h1
    let A := Set.range (fun (n : ℕ) => (T.npow n p))
    have hA : BddBelow (Subtype.val '' A) := by
      apply bddBelow_def.mpr
      use 0; intro z hz
      simp at hz
      obtain ⟨hz, hzz⟩ := hz
      exact hz.left
    let y : I := ⟨sInf (Subtype.val '' A), by
      constructor
      refine Real.sInf_nonneg ?_
      intro x hx
      simp at hx
      obtain ⟨hx, hxx⟩ := hx
      exact hx.left

      refine csInf_le hA ?_
      simp
      refine Set.mem_range.mpr ?_
      use 0
      simp
    ⟩

    have hay : y ∉ A := by
      by_contra hay
      apply Set.mem_range.mp at hay
      obtain ⟨n, hn⟩ := hay
      have yley2 : y ≤ T.mul y y :=
        calc y.1
          _ ≤ T.npow (2*n) p := by
              unfold y;
              refine csInf_le hA ?_;

              simp
              constructor
              exact (T.npow (2*n) p).2
              apply Set.mem_range.mpr
              use (2*n)
          _ = T.mul y y := by rw [two_mul, ← T.npow_add, hn]
      have yley : y ≥ T.mul y y := by exact T.mul_self_le_self y
      apply le_antisymm yley2 at yley

      have hynt : y ≠ 0 ∧ y ≠ 1 := by
        constructor
        apply unitInterval.pos_iff_ne_zero.mp
        calc 0
          _ < q := by exact unitInterval.pos_iff_ne_zero.mpr hqnt.left
          _ ≤ y := by exact le_of_le_of_eq (hpq n) hn
        apply unitInterval.lt_one_iff_ne_one.mp
        calc y
          _ ≤ p := by
              unfold y
              refine csInf_le hA ?_
              simp
              constructor
              exact p.2
              apply Set.mem_range.mpr
              use 1
              exact T.npow_one p
          _ < 1 := by exact unitInterval.lt_one_iff_ne_one.mpr hpnt.right

      unfold HasNontrivialIdempotent at h2
      push_neg at h2
      specialize h2 y hynt
      rw [← yley] at h2
      contradiction


    use σ p
    constructor
    unfold unitInterval.symm
    apply Subtype.mk_lt_mk.mpr
    simp
    apply unitInterval.lt_one_iff_ne_one.mpr
    exact hpnt.right

    intro δ hd
    have hexx : ∃ x ∈ (Subtype.val '' A), x < y+δ := by
      refine Real.lt_sInf_add_pos ?_ hd
      simp
      exact Set.range_nonempty fun n ↦ T.npow n p
    obtain ⟨x, hxA, hxlt⟩ := hexx
    have hxA2 : x ∈ (Subtype.val '' A) := by exact hxA
    simp at hxA2
    obtain ⟨hxI, hxA2⟩ := hxA2
    obtain ⟨n, hnp⟩ := hxA2
    simp at hnp

    use ⟨x, hxI⟩
    use y
    constructor
    apply abs_sub_lt_iff.mpr
    constructor

    simp
    exact sub_left_lt_of_lt_add hxlt
    apply sub_left_lt_of_lt_add
    calc y.1
      _ ≤ x := by exact csInf_le hA hxA
      _ < x+δ := by exact lt_add_of_pos_right x hd

    calc y
      _ < T.npow (n+1) p := by
          apply lt_of_le_of_ne
          apply csInf_le hA ?_
          simp
          constructor
          exact (T.npow (n+1) p).2
          apply Set.mem_range.mpr
          use (n+1)

          by_contra hynpow
          have hay2 : y ∈ A := by
            apply Set.mem_range.mpr
            use (n+1)
            symm; exact hynpow
          contradiction
      _ = T.mul p (T.npow n p) := by rfl
      _ = T.mul (σ (σ p)) ⟨x, hxI⟩ := by nth_rw 1 [← unitInterval.symm_symm p, hnp]

-- Theorem 10
theorem luk_of_I_charitable (L : FuzzyLogic T.toTnorm) :
  IsCharitable I L → Tnorm.Isomorphic Tnorm.LukTnorm.toTnorm T.toTnorm := by
    intro h
    apply luk_iso_of_nilpt
    contrapose h

    unfold IsCharitable
    simp
    use id
    constructor
    exact fun ⦃U⦄ a ↦ a
    apply pocat_for_id

    obtain h|h|h|h := left_tnorm_cases T
    contradiction

    -- Case 1: T has no zero divisors
    exact not_charitable_of_nzds T.toTnorm h

    -- Case 2: T has a nontrivial idempotent
    exact not_charitable_of_ntid T.toTnorm h

    -- Case 3: T is non-Archimedean and has no nontrivial idempotents
    exact not_charitable_of_nonarch_nntid T.toTnorm h
