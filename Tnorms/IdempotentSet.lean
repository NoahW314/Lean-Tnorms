import Tnorms.Defs
import Tnorms.Basic
import Tnorms.Examples
import Tnorms.Order
import Tnorms.Algebra


import Mathlib.Topology.UnitInterval

open unitInterval
open Classical


/-
The file proves Theorem 2.7 from Triangular Norms.
The statement proved here is slightly different from what the book has because
1. the book requires A to be countable, but this follows from the other conditions
2. the book requires that 0 in S, but again this follows from the other conditions
3. the book does not require that (b α) = (a β) → (b α) ∈ S, as the J α's can be combined
     and renamed to satisfy this condition.  But I can't figure out how to do this part in lean
-/

theorem tnorm_with_idpt_set_mp (S : Set I) : (∃ T : Tnorm, S = {p : I | T.mul p p = p}) →
  (∃ A : Set (I×I), ∃ a : A → I, ∃ b : A → I,
    ⋃ α : A, Set.Ioo (a α) (b α) ⊆ Sᶜ
    ∧ Sᶜ ⊆ ⋃ α : A, Set.Ioc (a α) (b α)
    ∧ (∀ α β : A, (Set.Ioo (a α) (b α)) ∩ (Set.Ioo (a β) (b β)) ≠ ∅ → α = β)
    ∧ (∀ α β : A, (b α) = (a β) → (b α) ∈ S)) := by
    intro h
    obtain ⟨T, h⟩ := h
    let B := Sᶜ
    let a' : B → I := fun p₀ => sSup {p : I | p < p₀ ∧ T.mul p p = p}
    let b' : B → I := fun p₀ => sInf {p : I | p₀ < p ∧ T.mul p p = p}
    let ab' : B → I×I := fun p₀ => (a' p₀, b' p₀)
    let A := Set.range ab'
    let a : A → I := fun pq : A => pq.1.1
    let b : A → I := fun pq : A => pq.1.2

    use A; use a; use b;

    have hax : ∀ p₀ : B, T.mul (a' p₀) (a' p₀) = (a' p₀) := by
      intro p₀
      apply antisymm (T.mul_le_left (a' p₀) (a' p₀))
      apply sSup_le
      intro p hp;
      let hp2 := Set.mem_setOf.mp hp
      obtain ⟨hpp, hpid⟩ := hp2
      rw [← hpid]
      apply T.mul_le_mul
      exact le_sSup hp; exact le_sSup hp

    have hap₀ : ∀ p₀ : B, a' p₀ < p₀ := by
      intro p₀
      apply lt_of_le_of_ne
      apply sSup_le
      intro p hp; rw[Set.mem_setOf] at hp
      exact le_of_lt hp.1

      by_contra happ
      specialize hax p₀
      rw [happ] at hax
      let hpb : ↑p₀ ∉ S := p₀.2
      rw [h, Set.mem_setOf] at hpb
      contradiction

    have hbp₀ : ∀ p₀ : B, p₀ ≤ b' p₀ := by
      intro p₀
      apply le_sInf
      intro p hp; rw [Set.mem_setOf] at hp
      exact le_of_lt hp.1

    have hable' : ∀ p₀ : B, (a' p₀) < (b' p₀) := by
      intro p₀
      apply lt_of_lt_of_le (hap₀ p₀)
      apply le_sInf
      intro p hp; rw [Set.mem_setOf] at hp
      exact le_of_lt hp.1

    have hooni : ∀ p₀ : B, ∀ p ∈ Set.Ioo (a' p₀) (b' p₀), T.mul p p ≠ p := by
      intro p₀ p hpo; rw [Set.mem_Ioo] at hpo
      contrapose hpo
      rw [not_and_or]; push_neg; push_neg at hpo

      by_cases hpeq : p = p₀
      rw [hpeq] at hpo
      let hpb : ↑p₀ ∈ Sᶜ := p₀.2
      rw [h, Set.mem_compl_iff, Set.mem_setOf] at hpb
      contradiction

      by_cases hpp : p < p₀
      left; apply le_sSup; rw [Set.mem_setOf]
      constructor; exact hpp; exact hpo

      push_neg at hpp; push_neg at hpeq; symm at hpeq
      apply lt_of_le_of_ne hpp at hpeq
      right; apply sInf_le; rw [Set.mem_setOf]
      constructor; exact hpeq; exact hpo

    -- Set.Ioo (a' p₀) (b' p₀) is the largest open interval set of nonidempotent elements containing p₀
    have hocni : ∀ p₀ : B, ∀ c d : I, (∀ p ∈ Set.Ioo c d, T.mul p p ≠ p) →
      Set.Ioo (a' p₀) (b' p₀) ⊆ Set.Ioo c d → Set.Ioo (a' p₀) (b' p₀) = Set.Ioo c d := by
        intro p₀ c d hrni hsr
        apply subset_antisymm hsr

        have hrap : a' p₀ ∉ Set.Ioo c d := by
          by_contra hapr
          specialize hrni (a' p₀) hapr
          specialize hax p₀
          contradiction

        have hr : ∀ r ∈ Set.Ioo c d, (a' p₀) < r := by
          intro r hr
          by_contra! harp
          by_cases hrp : r = a' p₀
          rw [← hrp] at hrap
          contradiction

          apply lt_of_le_of_ne harp at hrp
          rw [Set.mem_Ioo] at hr
          suffices (a' p₀) ∈ Set.Ioo c d by contradiction
          constructor
          exact lt_trans hr.1 hrp
          obtain ⟨y, hy⟩ := Set.nonempty_Ioo.mpr (hable' p₀)
          let hy2 := hsr hy
          rw [Set.mem_Ioo] at hy; rw [Set.mem_Ioo] at hy2
          exact lt_trans hy.1 hy2.2
        have hbc : c < (b' p₀) := by
          obtain ⟨y, hy⟩ := Set.nonempty_Ioo.mpr (hable' p₀)
          let hy2 := hsr hy
          rw [Set.mem_Ioo] at hy; rw [Set.mem_Ioo] at hy2
          exact lt_trans hy2.1 hy.2
        have hr2 : c ≤ (a' p₀) := by
          apply forall_lt_iff_le'.mp
          intro q hpq
          by_cases hq : b' p₀ ≤ q
          apply lt_of_lt_of_le hbc hq
          push_neg at hq
          have hqcd : q ∈ Set.Ioo c d := by
            apply hsr; constructor
            exact hpq; exact hq
          exact hqcd.1

        intro r hro; rw [Set.mem_Ioo] at hro; rw [Set.mem_Ioo]
        constructor; exact hr r hro

        by_contra! hbr
        let hy := exists_between hro.2
        obtain ⟨y, hy⟩ := hy
        let hby := lt_of_le_of_lt hbr hy.1
        apply sInf_lt_iff.mp at hby
        obtain ⟨p, hp⟩ := hby
        rw [Set.mem_setOf] at hp
        specialize hrni p ?_
        constructor
        calc c
          _ ≤ a' p₀ := hr2
          _ < p₀ := hap₀ p₀
          _ < p := hp.1.1
        exact lt_trans hp.2 hy.2

        exact hrni hp.1.2

    have hprwdjt : ∀ p₀ q₀ : B, p₀ ≠ q₀ → ((a' p₀ = a' q₀ ∧ b' p₀ = b' q₀) ∨
      (Set.Ioo (a' p₀) (b' p₀) ∩ Set.Ioo (a' q₀) (b' q₀) = ∅)) := by
        intro p₀ q₀ hpq
        by_cases hab : a' p₀ = a' q₀ ∧ b' p₀ = b' q₀
        left; exact hab
        right; contrapose! hab
        obtain ⟨x, hab⟩ := hab

        let R := Set.Ioo (a' p₀) (b' p₀) ∪ Set.Ioo (a' q₀) (b' q₀)
        let c := (a' p₀) ⊓ (a' q₀)
        let d := (b' p₀) ⊔ (b' q₀)
        have hrs : R = Set.Ioo c d := by
          unfold R; rw [Set.Ioo_union_Ioo']
          simp only [Set.mem_inter_iff, Set.mem_Ioo] at hab
          exact lt_trans hab.2.1 hab.1.2
          exact lt_trans hab.1.1 hab.2.2
        have hrni : ∀ p ∈ R, T.mul p p ≠ p := by
          intro p hrp
          rcases hrp with hpr|hpr
          exact hooni p₀ p hpr
          exact hooni q₀ p hpr
        have hrsp : Set.Ioo (a' p₀) (b' p₀) ⊆ R := Set.subset_union_left
        have hrsq : Set.Ioo (a' q₀) (b' q₀) ⊆ R := Set.subset_union_right
        rw [hrs] at hrni; rw [hrs] at hrsp; rw [hrs] at hrsq

        apply hocni p₀ c d hrni at hrsp
        apply hocni q₀ c d hrni at hrsq
        rw [← hrsp] at hrsq
        let hapql := (Set.Ioo_subset_Ioo_iff (hable' q₀)).mp hrsq.subset
        let hapqg := (Set.Ioo_subset_Ioo_iff (hable' p₀)).mp hrsq.superset

        constructor
        exact antisymm hapql.1 hapqg.1
        exact antisymm hapqg.2 hapql.2

    constructor; swap; constructor; swap; constructor
    intro α β hnon
    let hα := α.2; let hβ := β.2
    rw [Set.mem_range] at hα; rw [Set.mem_range] at hβ
    obtain ⟨p₀, hα⟩ := hα; obtain ⟨q₀, hβ⟩ := hβ
    unfold ab' at hα; unfold ab' at hβ

    by_cases hpq : p₀ = q₀
    rw [hpq] at hα; rw [hα] at hβ
    ext1; exact hβ

    specialize hprwdjt p₀ q₀ hpq
    unfold a b at hnon
    rw [← hα, ← hβ] at hnon; simp only at hnon
    simp only [hnon, or_false] at hprwdjt
    ext; rw [← hα, ← hβ]; simp only
    apply Subtype.coe_inj.mpr; exact hprwdjt.1
    rw [← hα, ← hβ]; simp only
    apply Subtype.coe_inj.mpr; exact hprwdjt.2

    swap; intro r hr
    rw [Set.mem_iUnion]
    use ⟨(ab' ⟨r, hr⟩), by apply Set.mem_range_self⟩
    constructor
    simp only [a, ab']
    exact hap₀ ⟨r, hr⟩
    simp only [b, ab']
    exact hbp₀ ⟨r, hr⟩

    swap; intro r hr
    rw [Set.mem_compl_iff, h, Set.mem_setOf]; push_neg
    rw [Set.mem_iUnion] at hr
    obtain ⟨α, hr⟩ := hr
    let hα := α.2
    rw [Set.mem_range] at hα; obtain ⟨p₀, hα⟩ := hα
    unfold ab' at hα
    unfold a b at hr; rw [← hα] at hr
    simp only at hr
    exact hooni p₀ r hr


    intro α β hab
    rw [hab, h, Set.mem_setOf]
    let hβ := β.2
    unfold A ab' at hβ
    rw [Set.mem_range] at hβ
    obtain ⟨p₀, hβ⟩ := hβ
    unfold a; rw [← hβ]
    simp only
    exact hax p₀

theorem tnorm_with_idpt_set_mpr (S : Set I) (h1S : 1 ∈ S) :
 (∃ A : Set (I×I), ∃ a b : A → I,
 ⋃ α : A, Set.Ioo (a α) (b α) ⊆ Sᶜ
  ∧ Sᶜ ⊆ ⋃ α : A, Set.Ioc (a α) (b α)
  ∧ (∀ α β : A, (Set.Ioo (a α) (b α)) ∩ (Set.Ioo (a β) (b β)) ≠ ∅ → α = β)
  ∧ (∀ α β : A, (b α) = (a β) → (b α) ∈ S))
  → (∃ T : Tnorm, S = {p : I | T.mul p p = p})
  := by
    intro h
    obtain ⟨A, a, b, hus, hsu, hpwdt, hend⟩ := h
    let A := {α : A | (a α) < (b α)}
    let J : A → Set I := fun α : A => if (b α) ∉ S then Set.Ioc (a α) (b α) else Set.Ioo (a α) (b α)
    have hrJa : ∀ α : A, ∀ r : I, r ∈ J α → a α < r := by
      intro α r hr
      by_cases hab : b α ∈ S
      simp only [J, hab, not_true_eq_false, reduceIte, Set.mem_Ioo] at hr
      exact hr.1

      simp only [J, hab, not_false_eq_true, reduceIte, Set.mem_Ioc] at hr
      exact hr.1
    have hrJb : ∀ α : A, ∀ r : I, r ∈ J α → r ≤ b α := by
      intro α r hr
      by_cases hab : b α ∈ S
      simp only [J, hab, not_true_eq_false, reduceIte, Set.mem_Ioo] at hr
      exact le_of_lt hr.2
      simp only [J, hab, not_false_eq_true, reduceIte, Set.mem_Ioc] at hr
      exact hr.2
    have hpwdt : ∀ α β : A, (∃ r, r ∈ J α ∧ r ∈ J β) → α = β := by
      intro α β hr
      obtain ⟨r, hα, hβ⟩ := hr
      apply Subtype.coe_inj.mp
      apply hpwdt α β
      refine Set.nonempty_iff_ne_empty'.mp ?_

      let hr1 := hrJa α r hα
      let hr2 := hrJa β r hβ
      have hr3 : max (a α) (a β) < r := by apply max_lt hr1 hr2
      obtain ⟨q, hql, hqr⟩ := exists_between hr3
      use q; constructor; constructor
      apply lt_of_le_of_lt ?_ hql; apply le_max_left
      exact lt_of_lt_of_le hqr (hrJb α r hα)
      constructor
      apply lt_of_le_of_lt ?_ hql; apply le_max_right
      exact lt_of_lt_of_le hqr (hrJb β r hβ)
    have hsJ : ∀ α : A, Set.Ioo (a α) (b α) ⊆ J α := by
      intro α
      by_cases haS : (b α) ∈ S
      simp only [J, haS, not_true_eq_false, reduceIte]; rfl
      simp only [J, haS, not_false_eq_true, reduceIte]
      exact Set.Ioo_subset_Ioc_self
    have haJ : ∀ α β : A, (a β) ∉ (J α) := by
      intro α β habJ
      by_cases hab : b α = a β
      specialize hend α β hab
      simp only [J, hend, not_true_eq_false, reduceIte, ← hab, Set.mem_Ioo] at habJ
      exact (lt_self_iff_false (b α)).mp habJ.2

      specialize hrJb α (a β) habJ
      apply lt_of_le_of_ne' hrJb at hab
      have hmax : (a β) < min (b α) (b β) := by apply lt_min hab β.2
      obtain ⟨r, hr⟩ := exists_between hmax
      suffices α = β by
        rw [this] at habJ
        specialize hrJa β (a β) habJ
        exact (lt_self_iff_false (a β)).mp hrJa
      apply hpwdt α β
      use r; constructor
      apply hsJ α; constructor
      apply lt_trans ?_ hr.1
      exact hrJa α (a β) habJ
      exact lt_of_lt_of_le hr.2 (min_le_left (b α) (b β))

      apply hsJ β; constructor; exact hr.1
      exact lt_of_lt_of_le hr.2 (min_le_right (b α) (b β))

    have hpqJ : ∀ α : A, ∀ p q : I, p ≤ q → a α < p → q ∈ J α → p ∈ J α := by
      intro α p q hpq hap hα
      by_cases hab : b α ∈ S
      simp only [J, hab, not_true_eq_false, reduceIte, Set.mem_Ioo]
      simp only [J, hab, not_true_eq_false, reduceIte, Set.mem_Ioo] at hα
      constructor; exact hap; exact lt_of_le_of_lt hpq hα.2

      simp only [J, hab, not_false_eq_true, reduceIte, Set.mem_Ioc]
      simp only [J, hab, not_false_eq_true, reduceIte, Set.mem_Ioc] at hα
      constructor; exact hap; exact le_trans hpq hα.2

    have hconnJ : ∀ p q r : I, p ≤ q → q ≤ r → (¬∃ α, p ∈ J α ∧ q ∈ J α) → (¬∃ α, q ∈ J α ∧ r ∈ J α) → (¬∃ α, p ∈ J α ∧ r ∈ J α) := by
      intro p q r hpq' hqr' hpq hqr
      contrapose! hpq
      obtain ⟨α, hpq⟩ := hpq; use α; constructor; exact hpq.1
      by_cases hab : b α ∈ S
      simp only [J, hab, not_true_eq_false, reduceIte, Set.mem_Ioo]
      simp only [J, hab, not_true_eq_false, reduceIte, Set.mem_Ioo] at hpq
      constructor; exact lt_of_lt_of_le hpq.1.1 hpq'; exact lt_of_le_of_lt hqr' hpq.2.2

      simp only [J, hab, not_false_eq_true, reduceIte, Set.mem_Ioc]
      simp only [J, hab, not_false_eq_true, reduceIte, Set.mem_Ioc] at hpq
      constructor; exact lt_of_lt_of_le hpq.1.1 hpq'; exact le_trans hqr' hpq.2.2
    have hconnJ' : ∀ r q p : I, r ≤ q → q ≤ p → (¬∃ α, q ∈ J α ∧ r ∈ J α) → (¬∃ α, p ∈ J α ∧ q ∈ J α) → (¬∃ α, p ∈ J α ∧ r ∈ J α) := by
      intro r q p hqr' hpq' hqr hpq
      simp only [And.comm]; simp only [And.comm] at hpq; simp only [And.comm] at hqr
      exact hconnJ r q p hqr' hpq' hqr hpq


    let T : Tnorm := {
      mul p q := if h : ∃ α : A, p ∈ (J α) ∧ q ∈ (J α) then a ↑(Classical.choose h) else p ⊓ q
      mul_assoc := by
        intro p q r
        by_cases hpq : ∃ α, p ∈ J α ∧ q ∈ J α
        simp only [hpq, reduceDIte, haJ, false_and, exists_false]

        by_cases hqr : ∃ β, q ∈ J β ∧ r ∈ J β
        simp only [hqr, reduceDIte, haJ, and_false, exists_false]
        let α := Classical.choose hpq; let β := Classical.choose hqr
        let hα := Classical.choose_spec hpq; let hβ := Classical.choose_spec hqr
        specialize hpwdt α β ?_; use q; constructor
        exact hα.2; exact hβ.1
        apply And.left at hα; apply And.right at hβ
        apply hrJa α p at hα; apply hrJa β r at hβ
        apply Subtype.coe_inj.mpr at hpwdt
        rw [hpwdt] at hα; rw [← hpwdt] at hβ
        apply le_of_lt at hα; apply le_of_lt at hβ
        rw [min_eq_right hα, min_eq_left hβ, hpwdt]


        simp only [hqr, reduceDIte]
        by_cases hqr' : q ≤ r
        simp only [min_eq_left hqr', hpq, reduceDIte]
        apply min_eq_left; apply le_trans ?_ hqr'; apply le_of_lt
        let α := Classical.choose hpq; let hα := Classical.choose_spec hpq
        exact hrJa α q hα.2

        push_neg at hqr'; apply le_of_lt at hqr'; simp only [min_eq_right hqr']
        suffices ¬∃ α, p ∈ J α ∧ r ∈ J α by
          simp only [this, reduceDIte]
          let α := Classical.choose hpq; let hα := Classical.choose_spec hpq
          suffices r ≤ a ↑(Classical.choose hpq) by
            rw [min_eq_right this, min_eq_right]
            apply le_trans this;
            exact le_of_lt (hrJa α p hα.1)
          contrapose! this
          use α; constructor; exact hα.1
          exact hpqJ α r q hqr' this hα.2
        contrapose! hqr
        obtain ⟨α, hpq⟩ := hpq; obtain ⟨β, hqr⟩ := hqr
        specialize hpwdt α β ?_; use p; constructor; exact hpq.1; exact hqr.1
        use α; constructor; exact hpq.2; rw [hpwdt]; exact hqr.2


        simp only [hpq, reduceDIte]
        by_cases hqr : ∃ β, q ∈ J β ∧ r ∈ J β
        simp only [hqr, reduceDIte, haJ, and_false, exists_false]
        by_cases hpq' : p ≤ q
        have hpr : ¬∃ α, p ∈ J α ∧ r ∈ J α := by
          contrapose! hpq
          obtain ⟨α, hpq⟩ := hpq; obtain ⟨β, hqr⟩ := hqr
          specialize hpwdt α β ?_; use r; constructor; exact hpq.2; exact hqr.2
          use α; constructor; exact hpq.1; rw [hpwdt]; exact hqr.1
        simp only [min_eq_left hpq', hpr, reduceDIte]
        apply inf_eq_inf_iff_left.mpr;
        let α := Classical.choose hqr; let hα := Classical.choose_spec hqr
        constructor
        apply le_trans (min_le_right p (a ↑α))
        exact le_of_lt (hrJa α r hα.2)
        apply le_trans (min_le_left p r)
        contrapose! hpq
        use α; constructor; swap; exact hα.1
        exact hpqJ α p q hpq' hpq hα.1

        push_neg at hpq'; apply le_of_lt at hpq';
        simp only [min_eq_right hpq', hqr, reduceDIte]
        symm; apply min_eq_right
        apply le_trans ?_ hpq'
        let α := Classical.choose hqr; let hα := Classical.choose_spec hqr
        exact le_of_lt (hrJa α q hα.1)


        simp only [hqr, reduceDIte]
        by_cases hpq' : q ≤ p
        simp only [min_eq_right hpq', hqr, reduceDIte]
        by_cases hqr' : q ≤ r
        simp only [min_eq_left hqr', hpq, reduceDIte]
        symm; exact min_eq_right hpq'
        push_neg at hqr'; apply le_of_lt at hqr'
        simp only [min_eq_right hqr']
        suffices ¬∃ α, p ∈ J α ∧ r ∈ J α by
          simp only [this, reduceDIte, min_eq_right (le_trans hqr' hpq')]
        exact hconnJ' r q p hqr' hpq' hqr hpq

        push_neg at hpq'; apply le_of_lt at hpq'
        simp only [min_eq_left hpq']
        by_cases hqr' : q ≤ r
        simp only [min_eq_left hqr', hpq, reduceDIte]
        suffices ¬∃ α, p ∈ J α ∧ r ∈ J α by
          simp only [this, reduceDIte, min_eq_left (le_trans hpq' hqr'), min_eq_left hpq']
        exact hconnJ p q r hpq' hqr' hpq hqr
        push_neg at hqr'; apply le_of_lt at hqr'
        simp only [min_eq_right hqr']

      mul_comm := by
        intro p q
        simp only [min_comm, and_comm]
      mul_one := by
        intro p
        suffices ∀ α : A, 1 ∉ J α by
          simp only [this, and_false, exists_false, reduceDIte]
          apply min_eq_left
          exact le_one p
        intro α; unfold J
        by_cases hab : b α ∈ S
        simp only [hab, not_true_eq_false, reduceIte, Set.mem_Ioo, not_and_or]
        push_neg; right; exact le_one (b α)

        simp only [hab, not_false_eq_true, reduceIte, Set.mem_Ioc, not_and_or]
        push_neg; right; apply lt_of_le_of_ne (le_one (b α))
        contrapose! hab
        rw [Set.Icc.coe_eq_one] at hab
        rw [hab]; exact h1S
      mul_le_mul_left := by
        intro p q hpq r
        by_cases hrp : ∃ α : A, r ∈ J α ∧ p ∈ J α
        by_cases hrq : ∃ α : A, r ∈ J α ∧ q ∈ J α

        simp only [hrp, hrq, reduceDIte]
        apply le_of_eq
        congr; ext α; constructor
        intro hr
        obtain ⟨β, hrq⟩ := hrq
        suffices α = β by
          rw [this]; exact hrq
        apply hpwdt α β
        use r; constructor; exact hr.1; exact hrq.1

        intro hr
        obtain ⟨β, hrp⟩ := hrp
        suffices α = β by
          rw [this]; exact hrp
        apply hpwdt α β
        use r; constructor; exact hr.1; exact hrp.1


        simp only [hrp, hrq, reduceDIte]
        apply le_min
        let hα := Classical.choose_spec hrp
        apply And.left at hα
        apply hrJa at hα
        apply le_of_lt hα
        apply le_trans ?_ hpq
        let hα := Classical.choose_spec hrp
        apply And.right at hα
        apply hrJa at hα
        apply le_of_lt hα


        by_cases hrq : ∃ α : A, r ∈ J α ∧ q ∈ J α

        simp only [hrp, hrq, reduceDIte]
        apply le_trans (min_le_right r p)
        let hα := hrq
        obtain ⟨α, hrq⟩ := hrq
        suffices ht : p ≤ a α by
          suffices a α = a ↑(Classical.choose hα) by
            rw [← this]; exact ht
          congr
          apply hpwdt α (Classical.choose hα)
          use r; constructor; exact hrq.1
          exact (Classical.choose_spec hα).1
        have haq : p < b α := by
          by_cases hpq' : p = q
          rw [← hpq'] at hrq
          rw [not_exists] at hrp
          specialize hrp α
          contradiction

          apply lt_of_le_of_ne hpq at hpq'
          apply lt_of_lt_of_le hpq'
          exact hrJb α q hrq.2
        push_neg at hrp
        specialize hrp α hrq.1
        unfold J at hrp
        by_cases hab : b α ∈ S
        simp only [hab, not_true_eq_false, reduceIte, Set.mem_Ioo, haq, and_true] at hrp
        push_neg at hrp; exact hrp
        simp only [hab, not_false_eq_true, reduceIte, Set.mem_Ioc, (le_of_lt haq), and_true] at hrp
        push_neg at hrp; exact hrp



        simp only [hrp, hrq, reduceDIte]
        exact inf_le_inf_left r hpq
    }

    use T; ext p; constructor; intro hp

    rw [Set.mem_setOf]
    suffices ∀ α : A, p ∉ (J α) by
      simp only [T, this, false_and, exists_false, reduceDIte, min_self]
    intro α
    rw [Set.subset_compl_comm] at hus
    let hpS := hp; apply hus at hp
    rw [Set.mem_compl_iff, Set.mem_iUnion] at hp
    push_neg at hp
    specialize hp α

    by_cases hbα : (b α) ∉ S
    simp only [J, hbα, not_false_eq_true, ↓reduceIte]

    suffices p ∉ Set.Ioo (a α) (b α) ∪ {(b α)} by
      rw [Set.Ioo_union_right α.2] at this
      exact this
    rw [Set.mem_union, not_or, Set.mem_singleton_iff]
    constructor; exact hp
    by_contra!; rw [this] at hpS
    exact hbα hpS

    push_neg at hbα
    simp only [J, hbα, not_true_eq_false, reduceIte]
    exact hp



    intro hp; rw [Set.mem_setOf] at hp
    contrapose! hp
    let hpS := hp
    rw [← Set.mem_compl_iff] at hp
    apply hsu at hp; rw [Set.mem_iUnion] at hp
    obtain ⟨α, hp⟩ := hp
    let α' : A := ⟨α, by
      unfold A; rw [Set.mem_setOf]
      apply lt_of_lt_of_le hp.1 hp.2
    ⟩

    suffices p ∈ J α' by
      have hα : ∃ α' : A, p ∈ J α' := by use α'
      simp only [T, and_self, hα, reduceDIte]
      let hαp := Classical.choose_spec hα
      by_contra!; symm at this
      unfold J at hαp
      rw [← this] at hαp

      by_cases hbS : b ↑(Classical.choose hα) ∈ S
      simp only [hbS, not_true_eq_false, reduceIte, Set.mem_Ioo] at hαp
      exact (lt_self_iff_false p).mp hαp.1

      simp only [hbS, not_false_eq_true, reduceIte, Set.mem_Ioc] at hαp
      exact (lt_self_iff_false p).mp hαp.1

    by_cases hbα : b α' ∈ S
    simp only [J, hbα, not_true_eq_false, reduceIte]
    suffices p ≠ b α' by
      rw [← Set.Ioc_diff_right, Set.mem_diff, Set.mem_singleton_iff]
      constructor; exact hp; exact this
    by_contra!
    rw [this] at hpS
    exact hpS hbα

    simp only [J, hbα, not_false_eq_true, reduceIte]
    exact hp


theorem tnorm_with_idpt_set (S : Set I) (h1S : 1 ∈ S) : (∃ T : Tnorm, S = {p : I | T.mul p p = p}) ↔
  (∃ A : Set (I×I), ∃ a : A → I, ∃ b : A → I,
  ⋃ α : A, Set.Ioo (a α) (b α) ⊆ Sᶜ
  ∧ Sᶜ ⊆ ⋃ α : A, Set.Ioc (a α) (b α)
  ∧ (∀ α β : A, (Set.Ioo (a α) (b α)) ∩ (Set.Ioo (a β) (b β)) ≠ ∅ → α = β)
  ∧ (∀ α β : A, (b α) = (a β) → (b α) ∈ S)) := by
    constructor;
    exact tnorm_with_idpt_set_mp S
    exact tnorm_with_idpt_set_mpr S h1S
