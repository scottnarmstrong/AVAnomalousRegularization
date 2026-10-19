-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleWords.CoreScalarPackage
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
public import Mathlib.Data.Int.Star

/-! **The regions of a package cut to its window**. `SeamOldScalarStatement` gives the old
letters quiet only on `reg.quiet ∩ [t₀, t₀ + S]`, while a word piece (`IsWordPiece`) asks for
quiet on all of its regions' quiet set. The regions `reg.inWindow t₀ S` keep the quiet times
inside the window and the pulses whose buffered hull `[lo - D_q, hi + D_q]` is nonempty; the
joins and the buffer are unchanged. Every field of the package passes to them
(`CoreScalarPackage.inWindow`): a dropped pulse has empty core `[lo, hi]` (as `D_q ≥ 0`), so it
covers no time, and a kept pulse has its buffers inside the hull, hence inside the window. The
fibre data are the same (the field `actual` is unchanged), so the gauge does not change.

Degenerate cases:
- No pulses: only the quiet set changes.
- Every pulse kept, `reg.quiet ⊆ [t₀, t₀ + S]`: the same regions up to reindexing.
- `D_q = 0`: a pulse is kept iff `lo ≤ hi`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity

/-- The pulses whose buffered hull is nonempty. -/
abbrev BlockRegions.KeptPulse (reg : BlockRegions) : Type :=
  {p : Fin reg.P // reg.lo p ≤ reg.hi p + reg.buffer}

instance (reg : BlockRegions) : Finite reg.KeptPulse := Subtype.finite

/-- The kept pulse of a new index. -/
def BlockRegions.keptPulse (reg : BlockRegions) (i : Fin (Nat.card reg.KeptPulse)) :
    Fin reg.P :=
  ((Finite.equivFin reg.KeptPulse).symm i).1

theorem BlockRegions.keptPulse_le (reg : BlockRegions) (i : Fin (Nat.card reg.KeptPulse)) :
    reg.lo (reg.keptPulse i) ≤ reg.hi (reg.keptPulse i) + reg.buffer :=
  ((Finite.equivFin reg.KeptPulse).symm i).2

/-- The regions cut to the window `[t₀, t₀ + S]`. -/
def BlockRegions.inWindow (reg : BlockRegions) (t₀ S : ℝ) : BlockRegions where
  P := Nat.card reg.KeptPulse
  lo := fun i => reg.lo (reg.keptPulse i)
  hi := fun i => reg.hi (reg.keptPulse i)
  orient := fun i => reg.orient (reg.keptPulse i)
  quiet := reg.quiet ∩ Set.Icc t₀ (t₀ + S)
  marks := reg.marks
  joins := reg.joins
  buffer := reg.buffer

theorem BlockRegions.inWindow_quiet (reg : BlockRegions) (t₀ S : ℝ) :
    (reg.inWindow t₀ S).quiet = reg.quiet ∩ Set.Icc t₀ (t₀ + S) := rfl

/-- Transversality on the pulses passes to the kept pulses. -/
theorem IsTransverseOnPulses.inWindow {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    {edge : ConstituentEdges D h} {reg : BlockRegions} (t₀ S : ℝ)
    (ht : IsTransverseOnPulses edge (fun p : Fin reg.P => Set.Icc (reg.lo p) (reg.hi p))
      reg.orient) :
    IsTransverseOnPulses edge
      (fun p : Fin (reg.inWindow t₀ S).P =>
        Set.Icc ((reg.inWindow t₀ S).lo p) ((reg.inWindow t₀ S).hi p))
      (reg.inWindow t₀ S).orient :=
  fun p => ht (reg.keptPulse p)

/-- **The package on the regions cut to its window.** -/
def CoreScalarPackage.inWindow {K : ScalarConstants} {η : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ}
    {reg : BlockRegions} (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) :
    CoreScalarPackage K η G v t₀ S ϖ (reg.inWindow t₀ S) where
  consts_pos := pkg.consts_pos
  actual := pkg.actual
  contraction := pkg.contraction
  high_smoothing := pkg.high_smoothing
  quiet_zero := fun t ht => pkg.quiet_zero t ⟨ht.1.1, ht.2⟩
  quiet_mean := fun ξ hξ a b hab hq hw =>
    pkg.quiet_mean ξ hξ a b hab (hq.trans Set.inter_subset_left) hw
  quiet_gap := fun ξ hξ a b hab hq hw =>
    pkg.quiet_gap ξ hξ a b hab (hq.trans Set.inter_subset_left) hw
  cover := by
    intro t ht
    rcases pkg.cover t ht with hq | ⟨p, hp⟩
    · exact Or.inl ⟨hq, ht⟩
    · have hkeep : reg.lo p ≤ reg.hi p + reg.buffer := by
        linarith [hp.1, hp.2, pkg.buffer_nonneg]
      refine Or.inr ⟨Finite.equivFin reg.KeptPulse ⟨p, hkeep⟩, ?_⟩
      have he : reg.keptPulse (Finite.equivFin reg.KeptPulse ⟨p, hkeep⟩) = p := by
        unfold BlockRegions.keptPulse
        rw [Equiv.symm_apply_apply]
      show t ∈ Set.Icc (reg.lo (reg.keptPulse _)) (reg.hi (reg.keptPulse _))
      rw [he]
      exact hp
  buffer_nonneg := pkg.buffer_nonneg
  buffer_le := pkg.buffer_le
  joins_ge := by
    show 2 * Nat.card reg.KeptPulse ≤ reg.joins
    have hc : Nat.card reg.KeptPulse ≤ reg.P := by
      calc Nat.card reg.KeptPulse ≤ Nat.card (Fin reg.P) :=
            Finite.card_subtype_le (fun p : Fin reg.P => reg.lo p ≤ reg.hi p + reg.buffer)
        _ = reg.P := Nat.card_fin _
    linarith [pkg.joins_ge]
  buffer_inside := fun p => pkg.buffer_inside (reg.keptPulse p)
  buffer_quiet := by
    intro p
    have hk := reg.keptPulse_le p
    have hin := pkg.buffer_inside (reg.keptPulse p)
    have hq := pkg.buffer_quiet (reg.keptPulse p)
    refine ⟨fun t ht => ⟨hq.1 ht, hin ⟨ht.1, ?_⟩⟩, fun t ht => ⟨hq.2 ht, hin ⟨?_, ht.2⟩⟩⟩
    · have h2 : t < reg.lo (reg.keptPulse p) := ht.2
      linarith
    · have h1 : reg.hi (reg.keptPulse p) < t := ht.1
      linarith
  ext := fun p => pkg.ext (reg.keptPulse p)
  ext_local := fun p => pkg.ext_local (reg.keptPulse p)
  ext_shear := fun p => pkg.ext_shear (reg.keptPulse p)
  ext_drift := fun p => pkg.ext_drift (reg.keptPulse p)
  ext_agree := fun p => pkg.ext_agree (reg.keptPulse p)
  replace_graph := fun j p => pkg.replace_graph j (reg.keptPulse p)
  replace_row := fun j p => pkg.replace_row j (reg.keptPulse p)
  replace_symbol := fun p => pkg.replace_symbol (reg.keptPulse p)
  weights := pkg.weights
  neg_adjoint := pkg.neg_adjoint

end AVRegularity
