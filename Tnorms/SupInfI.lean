import Mathlib.Topology.UnitInterval




open unitInterval


section namespace UnitInterval

-- Is this needed?
instance : DenselyOrdered unitInterval where
  dense p q := by
    intro hpq
    have hp : p < ((p.1+q)/2) := left_lt_add_div_two.mpr hpq
    have hq : ((p.1+q)/2) < q := add_div_two_lt_right.mpr hpq
    use ⟨(p.1+q)/2, by
      apply le_of_lt at hp; apply le_of_lt at hq; constructor
      exact le_trans p.2.1 hp
      exact le_trans hq q.2.2
      ⟩
    constructor; exact hp; exact hq


theorem sInf_le_iff {s : Set I} (h : s.Nonempty) {a : I} : sInf s ≤ a ↔ ∀ (ε:ℝ), ε > 0 → ∃ x ∈ s, x < a + ε := by
  have h' : (Subtype.val '' s).Nonempty := Set.Nonempty.image Subtype.val h
  have hbdd : BddBelow (Subtype.val '' s) := by
    apply bddBelow_def.mpr
    use 0; intro y hy;
    simp only [Set.mem_image, Subtype.exists, Set.mem_Icc, exists_and_right, exists_eq_right] at hy
    obtain ⟨hyI, hy⟩ := hy
    exact hyI.1

  constructor; intro ha; apply Subtype.coe_le_coe.mpr at ha
  rw [Set.Icc.coe_sInf zero_le_one h] at ha

  apply (Real.sInf_le_iff hbdd h').mp at ha
  intro ε he; specialize ha ε he
  obtain ⟨x, hx, ha⟩ := ha
  simp only [Set.mem_image, Subtype.exists, Set.mem_Icc, exists_and_right, exists_eq_right] at hx
  obtain ⟨hxI, hxS⟩ := hx
  use ⟨x, hxI⟩

  intro ha; apply Subtype.coe_le_coe.mp
  rw [Set.Icc.coe_sInf zero_le_one h]
  apply (Real.sInf_le_iff hbdd h').mpr
  intro ε he; specialize ha ε he
  obtain ⟨x, hxS, ha⟩ := ha
  use x.1; constructor;
  simp only [Set.mem_image, Subtype.exists, Set.mem_Icc, exists_and_right,
    exists_eq_right, Subtype.coe_eta, exists_prop]
  constructor; exact x.2; exact hxS; exact ha


theorem le_sSup_iff {s : Set I} (h : s.Nonempty) {a : I} : a ≤ sSup s ↔ ∀ (ε:ℝ), ε < 0 → ∃ x ∈ s, a + ε < x := by
  have h' : (Subtype.val '' s).Nonempty := Set.Nonempty.image Subtype.val h
  have hbdd : BddAbove (Subtype.val '' s) := by
    apply bddAbove_def.mpr
    use 1; intro y hy
    simp only [Set.mem_image, Subtype.exists, Set.mem_Icc, exists_and_right, exists_eq_right] at hy
    obtain ⟨hyI, hy⟩ := hy
    exact hyI.2

  constructor; intro ha; apply Subtype.coe_le_coe.mpr at ha
  rw [Set.Icc.coe_sSup zero_le_one h] at ha
  apply (Real.le_sSup_iff hbdd h').mp at ha
  intro ε he; specialize ha ε he
  obtain ⟨x, hxS, ha⟩ := ha
  simp only [Set.mem_image, Subtype.exists, Set.mem_Icc, exists_and_right, exists_eq_right] at hxS
  obtain ⟨hxI, hxS⟩ := hxS
  use ⟨x, hxI⟩

  intro ha; apply Subtype.coe_le_coe.mp
  rw [Set.Icc.coe_sSup zero_le_one h]
  apply (Real.le_sSup_iff hbdd h').mpr
  intro ε he; specialize ha ε he
  obtain ⟨x, hxS, ha⟩ := ha
  use x.1; constructor
  simp only [Set.mem_image, Subtype.exists, Set.mem_Icc, exists_and_right, exists_eq_right,
    Subtype.coe_eta, exists_prop]
  constructor; exact x.2; exact hxS; exact ha




end UnitInterval
