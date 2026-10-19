-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.BoxJoint
import AVRegularity.EntryWeak.JointSourceCongruence

/-! **The admissible slow offsets of a lift.** `ladderOmega D b j₀ m k A ρ` (the slow offsets
`X` whose recentering `A^{[ρX]}` is admissible) is open (`isOpen_ladderOmega`), and contains `0`
when `A` is admissible (`zero_mem_ladderOmega`). Recentering moves only the center of the last
child, continuously (`continuous_recenterShift`); the carrier conditions on it are strict. -/

@[expose] public noncomputable section

open Homogenization AVRegularity Set

namespace AVRegularity.Providers.GenSem

theorem recenter_ctxLevel (D : OCData) (ch : RealChain) (h : Vec 2) :
    (ch.recenter D h).ctxLevel = ch.ctxLevel := by
  rcases List.eq_nil_or_concat ch.children with hc | ⟨cs, c, hc⟩
  · rw [recenter_nil D ch hc]; rfl
  · rw [List.concat_eq_append] at hc
    rw [recenter_snoc D ch cs c hc h]
    simp [RealChain.ctxLevel, RealChain.lastLevel, hc]

theorem continuous_recenterShift (D : OCData) (ch : RealChain) (c : ChainChild) :
    Continuous (recenterShift D ch c) := by
  unfold recenterShift shiftOf
  have h := EntryWeakProofs.geomSpatialSmooth_geom D ch.dropLastChild
    ((ch.dropLastChild).geom D).2.2 (D.slotAnchor (ch.lastLevel + 1) ch.slot)
  exact ((h.continuous.comp (continuous_const.add continuous_id)).sub continuous_const).sub
    continuous_const

/-- The carrier conditions of a chain whose children are `cs ++ [c']`, split at the last child. -/
theorem isCarrierChain_snoc_iff (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (mres : ℝ)
    (ch : RealChain) (cs : List ChainChild) (c' : ChainChild) (hc : ch.children = cs ++ [c']) :
    IsCarrierChain D b j₀ i p mres ch ↔
      ((ch.ctxLevel = i ∧ j₀ ≤ ch.baseLevel + 1 ∧ ch.slots.length = cs.length + 2 ∧
        ch.slot = p ∧ (∀ q ∈ ch.slots, Odd q) ∧
        (∀ k : ℕ, ∀ hk : k + 1 < ch.slots.length,
          IsScheduledIn D (ch.baseLevel + 1 + k) (ch.slots[k + 1]) (ch.slots[k]))) ∧
        (∀ k : ℕ, ∀ hk : k < cs.length,
          ∑ a : Fin 2, |(cs[k]).center a| < (1 + mres) * b / 4 * D.eps (ch.baseLevel + 1 + k))) ∧
      ∑ a : Fin 2, |c'.center a| < (1 + mres) * b / 4 * D.eps (ch.baseLevel + 1 + cs.length) := by
  unfold IsCarrierChain
  have hlen : ch.children.length = cs.length + 1 := by simp [hc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨⟨⟨h1, h2, by omega, h4, h5, h6⟩, fun k hk => ?_⟩, ?_⟩
    · have := h7 k (by omega)
      simpa [hc, List.getElem_append_left hk] using this
    · have := h7 cs.length (by omega)
      simpa [hc] using this
  · rintro ⟨⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩, h8⟩
    refine ⟨h1, h2, by omega, h4, h5, h6, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k cs.length with hlt | hge
    · have := h7 k hlt
      simpa [hc, List.getElem_append_left hlt] using this
    · have hk' : k = cs.length := by omega
      subst hk'
      simpa [hc] using h8

/-- Admissibility of a recentered chain with a last child: the conditions independent of the
offset, and the strict bound on the moved last child. -/
theorem admissible_recenter_iff (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (A : RealChain)
    (cs : List ChainChild) (c : ChainChild) (hc : A.children = cs ++ [c]) (h : Vec 2) :
    IsAdmissibleChain D b j₀ i p (A.recenter D h) ↔
      ((A.ctxLevel = i ∧ j₀ ≤ A.baseLevel + 1 ∧ A.slots.length = cs.length + 2 ∧
        A.slot = p ∧ (∀ q ∈ A.slots, Odd q) ∧
        (∀ k : ℕ, ∀ hk : k + 1 < A.slots.length,
          IsScheduledIn D (A.baseLevel + 1 + k) (A.slots[k + 1]) (A.slots[k]))) ∧
        (∀ k : ℕ, ∀ hk : k < cs.length,
          ∑ a : Fin 2, |(cs[k]).center a| < (1 + 2) * b / 4 * D.eps (A.baseLevel + 1 + k))) ∧
      ∑ a : Fin 2, |(c.center + recenterShift D A c h) a| <
        (1 + 2) * b / 4 * D.eps (A.baseLevel + 1 + cs.length) := by
  have hch : (A.recenter D h).children = cs ++
      [⟨c.center + recenterShift D A c h, c.phase + (D.eps A.lastLevel)⁻¹ • recenterShift D A c h⟩] := by
    rw [recenter_snoc D A cs c hc h]
  have hb := recenter_baseLevel D A h
  have hlev := recenter_ctxLevel D A h
  have hslot : (A.recenter D h).slot = A.slot := by
    simp only [RealChain.slot, hb.2]
  unfold IsAdmissibleChain
  rw [isCarrierChain_snoc_iff D b j₀ i p 2 _ cs _ hch]
  simp only [hlev, hb.1, hb.2, hslot]

/-- **The admissible recentering offsets form an open set.** -/
theorem isOpen_admissible_recenter (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (A : RealChain) :
    IsOpen {h : Vec 2 | IsAdmissibleChain D b j₀ i p (A.recenter D h)} := by
  rcases List.eq_nil_or_concat A.children with hc | ⟨cs, c, hc⟩
  · have e : {h : Vec 2 | IsAdmissibleChain D b j₀ i p (A.recenter D h)} =
        {_h : Vec 2 | IsAdmissibleChain D b j₀ i p A} := by
      ext h
      simp only [mem_ofPred_eq, recenter_nil D A hc h]
      rfl
    rw [e]
    exact isOpen_const
  · rw [List.concat_eq_append] at hc
    have e : {h : Vec 2 | IsAdmissibleChain D b j₀ i p (A.recenter D h)} =
        {_h : Vec 2 | ((A.ctxLevel = i ∧ j₀ ≤ A.baseLevel + 1 ∧ A.slots.length = cs.length + 2 ∧
          A.slot = p ∧ (∀ q ∈ A.slots, Odd q) ∧
          (∀ k : ℕ, ∀ hk : k + 1 < A.slots.length,
            IsScheduledIn D (A.baseLevel + 1 + k) (A.slots[k + 1]) (A.slots[k]))) ∧
          (∀ k : ℕ, ∀ hk : k < cs.length,
            ∑ a : Fin 2, |(cs[k]).center a| < (1 + 2) * b / 4 * D.eps (A.baseLevel + 1 + k)))} ∩
        {h : Vec 2 | ∑ a : Fin 2, |(c.center + recenterShift D A c h) a| <
          (1 + 2) * b / 4 * D.eps (A.baseLevel + 1 + cs.length)} := by
      ext h
      simp only [mem_ofPred_eq, mem_inter_iff]
      exact admissible_recenter_iff D b j₀ i p A cs c hc h
    rw [e]
    refine isOpen_const.inter (isOpen_lt ?_ continuous_const)
    exact continuous_finsetSum _ fun a _ =>
      ((continuous_apply a).comp (continuous_const.add (continuous_recenterShift D A c))).abs

/-- **`ladderOmega` is open.** -/
theorem isOpen_ladderOmega (D : OCData) (b : ℝ) (j₀ m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ) :
    IsOpen (ladderOmega D b j₀ m k A ρ) :=
  (isOpen_admissible_recenter D b j₀ m k A).preimage (continuous_const_smul ρ)

/-- **`0 ∈ ladderOmega` for an admissible base chain.** -/
theorem zero_mem_ladderOmega {D : OCData} (hζ : IsFastProfile D.ζ) {b : ℝ} {j₀ m : ℕ} {k : ℤ}
    {A : RealChain} (hA : IsAdmissibleChain D b j₀ m k A) (ρ : ℝ) :
    (0 : Vec 2) ∈ ladderOmega D b j₀ m k A ρ := by
  show IsAdmissibleChain D b j₀ m k (A.recenter D (ρ • (0 : Vec 2)))
  rw [smul_zero, recenter_zero D hζ]
  exact hA

end AVRegularity.Providers.GenSem
