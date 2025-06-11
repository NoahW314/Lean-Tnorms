import Tnorms.Defs
import Tnorms.Algebra
import Mathlib.Topology.UnitInterval
open unitInterval

namespace Tnorm

lemma cont_of_iso {φ : I → I} (hi : Isomorphism φ) : _root_.Continuous φ := by
  exact Monotone.continuous_of_surjective hi.2 hi.1.2

lemma uni_cont_of_iso {φ : I → I} (hi : Isomorphism φ) : UniformContinuous φ := by
  exact CompactSpace.uniformContinuous_of_continuous (cont_of_iso hi)

lemma iso_is_strict_mono {φ : I → I} (hi : Isomorphism φ) : StrictMono φ :=
    Monotone.strictMono_of_injective hi.2 hi.1.1

lemma mono_inv_is_mono {φ : I → I} (hi : Isomorphism φ) : Monotone (Function.invFun φ) := by
    let φ' := Function.invFun φ
    intro p q
    contrapose
    intro hpq
    apply lt_of_not_ge at hpq
    apply not_le_of_gt
    apply_fun φ at hpq

    have hφ : Function.RightInverse φ' φ := by exact Function.rightInverse_invFun hi.1.2
    let hφ2 := hφ
    specialize hφ p; specialize hφ2 q;
    rw [hφ, hφ2] at hpq
    exact hpq
    exact iso_is_strict_mono hi

lemma iso_inv_is_iso {φ : I → I} (hi : Isomorphism φ) : Isomorphism (Function.invFun φ) := by
  constructor
  refine Function.bijective_iff_has_inverse.mpr ?_
  use φ
  constructor
  exact Function.rightInverse_invFun hi.1.2
  exact Function.leftInverse_invFun hi.1.1

  exact mono_inv_is_mono hi

lemma iso_inv_is_iso_btwn {T₁ T₂ : Tnorm} {φ : I → I} (hi : IsomorphismBetween T₁ T₂ φ) :
  IsomorphismBetween T₂ T₁ (Function.invFun φ) := by
    constructor; exact iso_inv_is_iso hi.1
    intro p q
    nth_rw 1 [← Function.rightInverse_invFun hi.1.1.2 p, ← Function.rightInverse_invFun hi.1.1.2 q]
    rw [← hi.2, Function.leftInverse_invFun hi.1.1.1]


lemma iso_comp {φ ψ : I → I} (hiφ : Isomorphism φ) (hiψ : Isomorphism ψ) : Isomorphism (φ ∘ ψ) := by
    constructor
    apply Function.Bijective.comp hiφ.1 hiψ.1
    apply Monotone.comp hiφ.2 hiψ.2


lemma iso_symm {T₁ T₂ : Tnorm} : Isomorphic T₁ T₂ → Isomorphic T₂ T₁ := by
    intro h
    obtain ⟨φ, h⟩ := h
    use Function.invFun φ; exact iso_inv_is_iso_btwn h

lemma iso_symm' {T₁ T₂ : Tnorm} : Isomorphic T₁ T₂ ↔ Isomorphic T₂ T₁ := by
    constructor
    exact iso_symm
    exact iso_symm

lemma id_iso : Isomorphism id := by
  constructor
  exact Function.bijective_id
  exact fun ⦃a b⦄ a ↦ a

lemma iso_rfl {T : Tnorm} : Isomorphic T T := by
  use id; constructor; exact id_iso
  intro p q; rw [id, id, id]

lemma iso_trans {T₁ T₂ T₃ : Tnorm} : Isomorphic T₁ T₂ → Isomorphic T₂ T₃ → Isomorphic T₁ T₃ := by
  intro ⟨φ₁, hφ₁, h12⟩ ⟨φ₂, hφ₂, h23⟩
  use φ₂ ∘ φ₁; constructor; exact iso_comp hφ₂ hφ₁
  intro p q
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply]
  rw [h12, h23]


lemma iso_one {φ : I → I} (hi : Isomorphism φ) : φ 1 = 1 := by
  by_contra h
  apply unitInterval.lt_one_iff_ne_one.mpr at h
  have hex : ∃ p : I, φ p = 1 := by exact hi.1.2 1
  obtain ⟨p, hp⟩ := hex
  nth_rw 2 [← hp] at h
  have hpl : p ≤ 1 := le_one p
  apply hi.2 at hpl
  apply lt_of_le_of_lt hpl at h
  exact (lt_self_iff_false (φ p)).mp h

lemma iso_zero {φ : I → I} (hi : Isomorphism φ) : φ 0 = 0 := by
  by_contra h
  apply unitInterval.pos_iff_ne_zero.mpr at h
  obtain ⟨p, hp⟩ := hi.1.2 0
  nth_rw 1 [← hp] at h
  have hpl : 0 ≤ p := nonneg p
  apply hi.2 at hpl
  apply lt_of_le_of_lt hpl at h
  exact (lt_self_iff_false (φ 0)).mp h


noncomputable
def apply_iso (T : Tnorm) {φ : I → I} (hi : Isomorphism φ) : Tnorm where
  mul p q := (Function.invFun φ) (T.mul (φ p) (φ q))
  mul_assoc p q r := by
    have hφ : Function.RightInverse (Function.invFun φ) φ := by apply Function.rightInverse_invFun hi.1.2
    rw [hφ, hφ, T.mul_assoc]
  mul_comm p q := by rw [T.mul_comm]
  mul_one p := by
    rw [iso_one hi, T.mul_one]
    apply Function.leftInverse_invFun hi.1.1
  mul_le_mul_left p q h r := by
    apply mono_inv_is_mono hi
    apply T.mul_le_mul_left
    apply hi.2 h

-- Proposition 2.28
lemma apply_is_iso {T : Tnorm} {φ : I → I} (hi : Isomorphism φ) : Isomorphic (apply_iso T hi) T := by
  use φ; constructor; exact hi
  intro p q
  apply Function.rightInverse_invFun hi.1.2
lemma apply_is_iso' {T : Tnorm} {φ : I → I} (hi : Isomorphism φ) : Isomorphic T (apply_iso T hi) := by
  apply iso_symm (apply_is_iso hi)

-- Remark 2.30
lemma apply_iso_comp {T : Tnorm} {φ ψ : I → I} (hφ : Isomorphism φ) (hψ : Isomorphism ψ) :
  (T.apply_iso hφ).apply_iso hψ = T.apply_iso (iso_comp hφ hψ) := by
    ext p q
    unfold apply_iso; simp only
    rw [Function.comp_apply, Function.comp_apply]
    have hfinComp : Function.invFun (φ ∘ ψ) = (Function.invFun ψ) ∘ (Function.invFun φ) := by
      apply Function.invFun_eq_of_injective_of_rightInverse (Function.Injective.comp hφ.1.1 hψ.1.1) ?_
      exact Function.RightInverse.comp (Function.rightInverse_invFun hφ.1.2) (Function.rightInverse_invFun hψ.1.2)
    rw [hfinComp, Function.comp_apply]

lemma apply_iso_id {T : Tnorm} : T.apply_iso (id_iso) = T := by
  ext p q; simp only [apply_iso, id]
  have hid : Function.invFun (id : I → I) = id := by
    exact Function.invFun_eq_of_injective_of_rightInverse (fun ⦃a₁ a₂⦄ a ↦ a) (congrFun rfl)
  rw [hid, id]

lemma apply_iso_inv {T : Tnorm} {φ : I → I} (hφ : Isomorphism φ) :
  (T.apply_iso hφ).apply_iso (iso_inv_is_iso hφ) = T := by
    rw [apply_iso_comp]
    nth_rw 2 [← T.apply_iso_id]
    congr
    apply Function.RightInverse.id (Function.rightInverse_invFun hφ.1.2)
lemma apply_iso_inv' {T : Tnorm} {φ : I → I} (hφ : Isomorphism φ) :
  (T.apply_iso (iso_inv_is_iso hφ)).apply_iso hφ = T := by
    rw [apply_iso_comp]
    nth_rw 2 [← T.apply_iso_id]
    congr
    apply Function.LeftInverse.id (Function.leftInverse_invFun hφ.1.1)


lemma mul_inv_iso {T₁ T₂ : Tnorm} {φ : I → I} (h : IsomorphismBetween T₁ T₂ φ) :
  ∀ p q : I, T₁.mul ((Function.invFun φ) p) ((Function.invFun φ) q) = (Function.invFun φ) (T₂.mul p q) := by
    intro p q
    obtain ⟨hφ, hm⟩ := h
    apply_fun φ; swap; exact hφ.1.1
    specialize hm ((Function.invFun φ) p) ((Function.invFun φ) q)
    rw [hm]
    have hr : ∀ r : I, φ ((Function.invFun φ) r) = r := by
      intro r; apply Function.rightInverse_invFun hφ.1.2
    rw [hr, hr, hr]


-- Show that isomorphisms preserve many of the properties of t-norms
section IsoInvariants

-- Continuouity, Left and Right

lemma iso_left_cont {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : T₂.LeftContinuous → T₁.LeftContinuous := by
  intro hc
  obtain ⟨φ, h⟩ := h
  intro x y p q hmx hmy hx hy
  specialize hc (φ ∘ x) (φ ∘ y) (φ p) (φ q) ?_ ?_ ?_ ?_
  apply Monotone.comp h.1.2 hmx
  apply Monotone.comp h.1.2 hmy
  apply Filter.Tendsto.comp ?_ hx
  exact Continuous.tendsto' (cont_of_iso h.1) p (φ p) rfl
  apply Filter.Tendsto.comp ?_ hy
  exact Continuous.tendsto' (cont_of_iso h.1) q (φ q) rfl

  simp only [Function.comp_apply, ← h.2] at hc
  have hr : ∀ r : I, ((Function.invFun φ) ∘ φ) r = r := by
    intro r; apply Function.leftInverse_invFun h.1.1.1
  have hrf : (fun n => T₁.mul (x n) (y n)) = (Function.invFun φ) ∘ (fun n => (φ (T₁.mul (x n) (y n)))) := by
    ext n; rw [Function.comp_apply]; nth_rw 1 [← hr (T₁.mul (x n) (y n)), Function.comp_apply]
  rw [hrf, ← hr (T₁.mul p q)]
  apply Filter.Tendsto.comp ?_ hc
  apply Continuous.tendsto' (cont_of_iso (iso_inv_is_iso h.1))
  rw [Function.comp_apply]

lemma iso_right_cont {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : T₂.RightContinuous → T₁.RightContinuous := by
  intro hc
  obtain ⟨φ, h⟩ := h
  intro x y p q hmx hmy hx hy
  specialize hc (φ ∘ x) (φ ∘ y) (φ p) (φ q) ?_ ?_ ?_ ?_
  apply Monotone.comp_antitone h.1.2 hmx
  apply Monotone.comp_antitone h.1.2 hmy
  apply Filter.Tendsto.comp ?_ hx
  exact Continuous.tendsto' (cont_of_iso h.1) p (φ p) rfl
  apply Filter.Tendsto.comp ?_ hy
  exact Continuous.tendsto' (cont_of_iso h.1) q (φ q) rfl

  simp only [Function.comp_apply, ← h.2] at hc
  have hr : ∀ r : I, ((Function.invFun φ) ∘ φ) r = r := by
    intro r; apply Function.leftInverse_invFun h.1.1.1
  have hrf : (fun n => T₁.mul (x n) (y n)) = (Function.invFun φ) ∘ (fun n => (φ (T₁.mul (x n) (y n)))) := by
    ext n; rw [Function.comp_apply]; nth_rw 1 [← hr (T₁.mul (x n) (y n)), Function.comp_apply]
  rw [hrf, ← hr (T₁.mul p q)]
  apply Filter.Tendsto.comp ?_ hc
  apply Continuous.tendsto' (cont_of_iso (iso_inv_is_iso h.1))
  rw [Function.comp_apply]

lemma iso_cont {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : T₂.Continuous → T₁.Continuous := by
  intro hc
  apply (cont_iff_left_right T₁).mpr; apply (cont_iff_left_right T₂).mp at hc
  constructor
  exact iso_left_cont h hc.1
  exact iso_right_cont h hc.2

-- Strictly Monotone, Cancellative, ConditionalCancellative
lemma iso_strict_mono {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : StrictlyMonotone T₂ → StrictlyMonotone T₁ := by
  intro hsm p hpp q r hqr
  obtain ⟨φ, h⟩ := h
  specialize hsm (φ p) ?_ (φ q) (φ r) ?_
  rw [← iso_zero h.1]
  apply iso_is_strict_mono h.1 hpp
  apply iso_is_strict_mono h.1 hqr
  rw [← h.2, ← h.2] at hsm
  contrapose! hsm
  apply h.1.2 hsm

lemma iso_canc {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : Cancellative T₂ → Cancellative T₁ := by
  intro hc
  apply (canc_iff_strictly_mono T₁).mpr
  apply (canc_iff_strictly_mono T₂).mp at hc
  exact iso_strict_mono h hc

lemma iso_cond_canc {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : ConditionalCancellative T₂ → ConditionalCancellative T₁ := by
  intro hcc p q r hmul hpr
  obtain ⟨φ, h⟩ := h
  apply_fun φ at hmul
  apply (iso_is_strict_mono h.1) at hpr
  rw [iso_zero h.1] at hpr
  rw [h.2, h.2] at hmul; rw [h.2] at hpr
  specialize hcc (φ p) (φ q) (φ r) hmul hpr
  exact h.1.1.1 hcc

-- Archimedean, LimitProperty

lemma iso_npow {T₁ T₂ : Tnorm} {φ : I → I} (h : IsomorphismBetween T₁ T₂ φ) (n : ℕ) (p : I) :
  φ (T₁.npow n p) = T₂.npow n (φ p) := by
    induction' n with n ih
    rw [T₁.npow_zero, T₂.npow_zero, iso_one h.1]
    rw [T₁.npow_succ, T₂.npow_succ, ← ih, h.2]

lemma iso_nontrivial {T₁ T₂ : Tnorm} {φ : I → I} (h : IsomorphismBetween T₁ T₂ φ) {p : I}
  (hpnt : IsNontrivial p) : IsNontrivial (φ p) := by
    contrapose! hpnt; unfold IsNontrivial; unfold IsNontrivial at hpnt
    rw [not_and_or]; rw [not_and_or] at hpnt; push_neg; push_neg at hpnt
    rcases hpnt with hpnt|hpnt
    left; rw [← iso_zero h.1] at hpnt
    apply h.1.1.1 hpnt
    right; rw [← iso_one h.1] at hpnt
    apply h.1.1.1 hpnt

lemma iso_arch {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : IsArchimedean T₂ → IsArchimedean T₁ := by
  intro ha p q hpnt hqnt
  obtain ⟨φ, h⟩ := h
  apply iso_nontrivial h at hpnt;  apply iso_nontrivial h at hqnt
  specialize ha (φ p) (φ q) hpnt hqnt
  obtain ⟨n, ha⟩ := ha; use n
  rw [← iso_npow h n p] at ha
  contrapose! ha
  apply h.1.2 ha

lemma iso_lp {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : HasLimitProperty T₂ → HasLimitProperty T₁ := by
  intro hlp
  apply (arch_iff_lp T₂).mpr at hlp
  apply (arch_iff_lp T₁).mp
  exact iso_arch h hlp

-- HasNontrivialIdempotent, HasNilpotentElement, HasZeroDivisors

lemma iso_ntid {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : HasNontrivialIdempotent T₂ → HasNontrivialIdempotent T₁ := by
  intro hid
  obtain ⟨φ, h⟩ := h
  obtain ⟨p, hpnt, hmul⟩ := hid
  use (Function.invFun φ) p; constructor
  apply iso_nontrivial (iso_inv_is_iso_btwn h) hpnt
  apply_fun φ; swap; exact h.1.1.1
  rw [h.2, Function.rightInverse_invFun h.1.1.2]
  exact hmul

lemma iso_nilpt_el {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : HasNilpotent T₂ → HasNilpotent T₁ := by
  intro hn
  obtain ⟨φ, h⟩ := h
  obtain ⟨p, hpnt, hn⟩ := hn
  use (Function.invFun φ) p; constructor
  exact iso_nontrivial (iso_inv_is_iso_btwn h) hpnt
  obtain ⟨n, hn⟩ := hn; use n
  apply_fun φ; swap; exact h.1.1.1
  rw [iso_npow h, Function.rightInverse_invFun h.1.1.2, iso_zero h.1]
  exact hn

lemma iso_zd {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : HasZeroDivisors T₂ → HasZeroDivisors T₁ := by
  intro hzd
  apply (nilpt_el_iff_zd T₂).mpr at hzd
  apply (nilpt_el_iff_zd T₁).mp
  exact iso_nilpt_el h hzd

-- Strict, Nilpotent

lemma iso_strict {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : Strict T₂ → Strict T₁ := by
  intro ⟨hc, hm⟩; constructor
  exact iso_cont h hc
  exact iso_strict_mono h hm

lemma iso_nilpt {T₁ T₂ : Tnorm} (h : Isomorphic T₁ T₂) : Nilpotent T₂ → Nilpotent T₁ := by
  intro ⟨hc, hn⟩; constructor
  exact iso_cont h hc
  intro p hpnt; obtain ⟨φ, h⟩ := h
  specialize hn (φ p) (iso_nontrivial h hpnt)
  obtain ⟨n, hn⟩ := hn; use n
  rw [← iso_npow h, ← iso_zero h.1] at hn
  apply h.1.1.1 hn


end IsoInvariants
