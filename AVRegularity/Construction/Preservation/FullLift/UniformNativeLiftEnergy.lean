-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
public import AVRegularity.Construction.Preservation.FullLift.NativeLiftedFieldCovarianceEnergy
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

section
section
/-! Bound every actual lifted field by the literal truncated retained readout and its given gradient. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedFieldW_readout_strong_energy_le
    {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (r : ℕ) (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (hk : r + N + 2 * p ≤ Naux)
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (hYw : ∀ v, MemLp (Yw v) 2 (volume.restrict (Set.Icc tp tf)))
    (hcompat : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      truncateTorusHk (Nat.le_succ Naux) (Yw v t) = Y v t)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hfield : IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (a t))
    (Sbar : ℝ) (hSbar : 0 ≤ Sbar) (hSSbar : S ≤ Sbar)
    {C rs : ℝ} (hC : 1 ≤ C) (hrs : 0 < rs) (hrse : rs ≤ D.eps G.level)
    (hρ : 0 < liftLength D G.level) (hν : 0 < D.κ G.level)
    (hB : 0 < D.κ (G.level - 1)) (hνB : D.κ G.level ≤ D.κ (G.level - 1))
    (hcell : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1)
    (hflow : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t,
      ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (r + 1 + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (r + 1 + N) C (liftLength D G.level))
    {cr Ccov : ℝ} (hcr : 0 < cr) (hcr1 : cr ≤ 1) (hCcov : 0 ≤ Ccov)
    (hcost : ∀ t ∈ Set.Icc tp tf,
      CycleComparison.Coarse.covPolyConst
        (CycleComparison.Coarse.fbCovConst (liftLength D G.level)
          (covPrimitive D G.level t) (r + N + 2 * p)) p ≤ Ccov) :
    strongEnergy rs (D.κ G.level) π tp tf u w ≤
      ((nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C) ^
        (1 / 2 : ℝ) * ENNReal.ofReal (Ccov * (cr⁻¹) ^ (r + N + 2 * p))) *
          strongEnergy (cr * liftLength D G.level) (D.κ (G.level - 1)) π tp tf
            (fun v t => truncateTorusHk hk
              (succReadout G.level (D.eps (G.level - 1)) η Naux (fun c => Y c t) v))
            (fun v t => truncateTorusHk (Nat.succ_le_succ hk)
              (succReadout G.level (D.eps (G.level - 1)) η (Naux + 1) (fun c => Yw c t) v)) := by
  have ha' : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((r + N + 1 : ℕ) : ℕ∞) (a t) := by
    simpa only [Nat.add_assoc, Nat.add_comm 1 N] using ha
  obtain ⟨Z, Zw, hZ, hZw, hmeas, hcov, hcovw, hzw⟩ :=
    liftedField_covariance_energy_input_exists G Gr G.level p Naux N H sX sZ r hk η tp tf
      hΛ hζ hν Y Yw hYw hcompat CcT PZ a u hfield.1 ha'
  exact native_liftedFieldW_covariance_strong_energy_le slotLifts hi hΛ hζ hband htorus
    r hreserve hrQ p Naux sX sZ η tp tf Y CcT PZ a u w hfield ha Sbar hSbar hSSbar
    hC hrs hrse hρ hν hB hνB hcell hflow Z Zw hZ hZw hmeas hcr hcr1 hCcov
    _ _ hzw hcov hcovw hcost

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The actual full-lift energy bound needs only a higher realization of the specified retained values. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedFieldW_readout_energy_of_higher_values
    {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (r : ℕ) (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (hk : r + N + 2 * p ≤ Naux)
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (hYw : ∀ v, MemLp (Yw v) 2 (volume.restrict (Set.Icc tp tf)))
    (hcompat : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      truncateTorusHk (Nat.le_succ Naux) (Yw v t) = Y v t)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hfield : IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w)
    (Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 3) (hr v.1.root))
    (heq : ∀ v, ∀ t ∈ Set.Icc tp tf,
      Y v t = truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi v t))
    (Sbar : ℝ) (hSbar : 0 ≤ Sbar) (hSSbar : S ≤ Sbar)
    {C rs : ℝ} (hC : 1 ≤ C) (hrs : 0 < rs) (hrse : rs ≤ D.eps G.level)
    (hρ : 0 < liftLength D G.level) (hν : 0 < D.κ G.level)
    (hB : 0 < D.κ (G.level - 1)) (hνB : D.κ G.level ≤ D.κ (G.level - 1))
    (hcell : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1)
    (hflow : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t,
      ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (r + 1 + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (r + 1 + N) C (liftLength D G.level))
    {cr Ccov : ℝ} (hcr : 0 < cr) (hcr1 : cr ≤ 1) (hCcov : 0 ≤ Ccov)
    (hcost : ∀ t ∈ Set.Icc tp tf,
      CycleComparison.Coarse.covPolyConst
        (CycleComparison.Coarse.fbCovConst (liftLength D G.level)
          (covPrimitive D G.level t) (r + N + 2 * p)) p ≤ Ccov) :
    strongEnergy rs (D.κ G.level) π tp tf u w ≤
      ((nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C) ^
        (1 / 2 : ℝ) * ENNReal.ofReal (Ccov * (cr⁻¹) ^ (r + N + 2 * p))) *
          strongEnergy (cr * liftLength D G.level) (D.κ (G.level - 1)) π tp tf
            (fun v t => truncateTorusHk hk
              (succReadout G.level (D.eps (G.level - 1)) η Naux (fun c => Y c t) v))
            (fun v t => truncateTorusHk (Nat.succ_le_succ hk)
              (succReadout G.level (D.eps (G.level - 1)) η (Naux + 1) (fun c => Yw c t) v)) := by
  have hreserve' : max (Naux - 2 * p) (r + 1 + N) + 2 * p + 2 ≤ Naux + 3 := by
    omega
  have ha := liftedField_classical_input_higher_regularity G Gr G.level p Naux N H sX sZ
    (r + 1 + N) (Naux + 3) (by omega) hreserve' η tp tf hΛ hζ Y Yhi heq
    CcT PZ a u hfield.1
  exact native_liftedFieldW_readout_strong_energy_le slotLifts hi hΛ hζ hband htorus
    r hreserve hrQ p Naux sX sZ η tp tf Y hk Yw hYw hcompat CcT PZ a u w hfield ha
    Sbar hSbar hSSbar hC hrs hrse hρ hν hB hνB hcell hflow hcr hcr1 hCcov hcost

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
section
/-! The actual full-lift energy bound needs only a higher realization of the specified retained values. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedFieldW_readout_energy_real_price
    {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (r : ℕ) (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (hk : r + N + 2 * p ≤ Naux)
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (hYw : ∀ v, MemLp (Yw v) 2 (volume.restrict (Set.Icc tp tf)))
    (hcompat : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      truncateTorusHk (Nat.le_succ Naux) (Yw v t) = Y v t)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hfield : IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w)
    (Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 3) (hr v.1.root))
    (heq : ∀ v, ∀ t ∈ Set.Icc tp tf,
      Y v t = truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi v t))
    (Sbar : ℝ) (hSbar : 0 ≤ Sbar) (hSSbar : S ≤ Sbar)
    {C rs : ℝ} (hC : 1 ≤ C) (hrs : 0 < rs) (hrse : rs ≤ D.eps G.level)
    (hρ : 0 < liftLength D G.level) (hν : 0 < D.κ G.level)
    (hB : 0 < D.κ (G.level - 1)) (hνB : D.κ G.level ≤ D.κ (G.level - 1))
    (hcell : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1)
    (hflow : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t,
      ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (r + 1 + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (r + 1 + N) C (liftLength D G.level))
    {cr Ccov : ℝ} (hcr : 0 < cr) (hcr1 : cr ≤ 1) (hCcov : 0 ≤ Ccov)
    (hcost : ∀ t ∈ Set.Icc tp tf,
      CycleComparison.Coarse.covPolyConst
        (CycleComparison.Coarse.fbCovConst (liftLength D G.level)
          (covPrimitive D G.level t) (r + N + 2 * p)) p ≤ Ccov)
    (Broot : ℝ) (hBroot : 0 ≤ Broot)
    (hprice : nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C ^
      (1 / 2 : ℝ) = ENNReal.ofReal Broot) :
    strongEnergy rs (D.κ G.level) π tp tf u w ≤
      ENNReal.ofReal (Broot * (Ccov * (cr⁻¹) ^ (r + N + 2 * p))) *
          strongEnergy (cr * liftLength D G.level) (D.κ (G.level - 1)) π tp tf
            (fun v t => truncateTorusHk hk
              (succReadout G.level (D.eps (G.level - 1)) η Naux (fun c => Y c t) v))
            (fun v t => truncateTorusHk (Nat.succ_le_succ hk)
              (succReadout G.level (D.eps (G.level - 1)) η (Naux + 1) (fun c => Yw c t) v)) := by
  have hfactor : nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C ^
      (1 / 2 : ℝ) * ENNReal.ofReal (Ccov * (cr⁻¹) ^ (r + N + 2 * p)) =
      ENNReal.ofReal (Broot * (Ccov * (cr⁻¹) ^ (r + N + 2 * p))) := by
    rw [hprice, ← ENNReal.ofReal_mul hBroot]
  have hb := native_liftedFieldW_readout_energy_of_higher_values slotLifts hi hΛ hζ hband htorus
    r hreserve hrQ p Naux sX sZ η tp tf Y hk Yw hYw hcompat CcT PZ a u w hfield Yhi heq
    Sbar hSbar hSSbar hC hrs hrse hρ hν hB hνB hcell hflow hcr hcr1 hCcov hcost
  exact hb.trans_eq (congrArg (fun q => q * strongEnergy (cr * liftLength D G.level)
    (D.κ (G.level - 1)) π tp tf _ _) hfactor)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Uniform native lift energy constants are chosen before data, stages, fields and weights. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
open EntryWeakProofs

theorem uniform_native_lift_energy_of_higher_values {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N r sX sZ p : ℕ, 2 ≤ Dm → 1 ≤ N →
    ∀ (Sbar cr : ℝ), 0 ≤ Sbar → 0 < cr → cr ≤ 1 →
    ∃ (Cenergy : ℝ) (m₀ : ℕ), 0 ≤ Cenergy ∧ 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (P : ProvParams)
      (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (M : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tA tB S θK G →
    S ≤ Sbar → m₀ ≤ G.level → G.level < D.term → j₀ ≤ G.level → G.fam.HasDepthAtMost H →
    (∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
    ∀ (Gr : GenStage D hr Dm bw j₀) (Naux : ℕ) (hk : r + N + 2 * p ≤ Naux),
    ∀ (η tp tf : ℝ)
      (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 3) (hr v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc tp tf,
      Y v t = truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi v t)) →
    ∀ (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)),
    (∀ v, MemLp (Yw v) 2 (volume.restrict (Set.Icc tp tf))) →
    (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      truncateTorusHk (Nat.le_succ Naux) (Yw v t) = Y v t) →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
      (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root)),
    IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w →
    ∀ (wgt : CompIn G.comps → ℝ), (wgt = fun _ => 1) ∨ wgt = G.marker law →
    ∀ rs : ℝ, 0 < rs → rs ≤ D.eps G.level →
    strongEnergy rs (D.κ G.level) (fun v => G.mass law v / wgt v ^ 2) tp tf u w ≤
      ENNReal.ofReal Cenergy * readoutEnergy law G Gr G.level η
        (cr * liftLength D G.level) hk wgt tp tf Y Yw := by
  classical
  obtain ⟨Λp, hΛp, hpack⟩ := uniform_native_weighted_slot_lifts hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Ccov0, hCcov0, Λc, hΛc, hcov⟩ := uniform_native_covariance_price hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λs, hΛs, hscale⟩ := native_lift_scale_bounds hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Λp (max Λc Λs), by omega, ?_⟩
  intro Λ hΛ bw hb Dm H N r sX sZ p hDm hN Sbar cr hSbar hcr hcr1
  let K := max sX (r + 1 + N + Dm)
  let k := max (r + 1) sZ
  obtain ⟨CG, Cw, Cj, mp, hmp, hp⟩ := hpack Λ (by omega) bw hb Dm H N K k sZ hDm hN
  obtain ⟨ms, hms, hs⟩ := hscale Λ (by omega)
  obtain ⟨mf, hmf, hf⟩ := uniform_native_physical_flow_jets α s q hα0 hα1 hs0 hs1 hq
    Λ (by omega) ζ hζ (r + 1 + N)
  let C := weakChartJetBudget (r + 1 + N) 0
  let Ccov := max 1 (CycleComparison.Coarse.covPolyConst (4 * Ccov0 * ((r + N + 2 * p : ℕ) : ℝ) ^ 2) p)
  obtain ⟨Broot, hBroot, hprice⟩ := nativeLiftStrongEnergyPrice_real_constant r
    (max k (sZ + 2)) Dm H N CG Cw Cj Sbar C
  refine ⟨Broot * (Ccov * (cr⁻¹) ^ (r + N + 2 * p)), max mp (max ms (mf + 1)),
    mul_nonneg hBroot (mul_nonneg (by dsimp [Ccov]; positivity) (pow_nonneg (inv_nonneg.mpr hcr.le) _)),
    by omega, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG hSSbar hm hmM hj hdepth hreserve hreserve2 hlength
    Gr Naux hk η tp tf Y Yhi heq Yw hYw hcompat CcT PZ a u w hfield wgt hwgt rs hrs hrse
  have htorus := hG.isTorusCompatible
  have hΛ1 : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hmterm : G.level ≤ D.term := hmM.le
  have hi : 1 ≤ G.level := by omega
  have ⟨hρ, hcell, hρE⟩ := hs D hDα hDq hDΛ hDζ hband G.level (by omega) hmterm
  have hcell' : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1 := by
    simpa only [OCData.kap, Nat.min_eq_left hmterm,
      Nat.min_eq_left ((Nat.sub_le G.level 1).trans hmterm)] using hcell
  have hE : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hρE' : liftLength D G.level ≤ D.eps (G.level - 1) := (div_le_one hE).mp hρE
  have hν := CycleReference.bandChain_pos hΛ1 hζD hband hmterm
  have hB := CycleReference.bandChain_pos hΛ1 hζD hband
    ((Nat.sub_le G.level 1).trans hmterm)
  have hνB := CycleReference.bandChain_step_ge hΛ1 hζD hband hi hmterm
  have hp' := hp hr D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG (by omega) hmM hj hdepth hreserve hreserve2 hlength wgt hwgt
  let slotLifts := fun slot => Classical.choice (hp' slot)
  have hres (slot : OddSlot) : r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2 := by
    have hc := (slotLifts slot).cap_le
    have hK : r + 1 + N + Dm ≤ K := Nat.le_max_right _ _
    omega
  have hflow : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t,
      ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (r + 1 + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (r + 1 + N) C (liftLength D G.level) := by
    intro t _ht j hj' hc
    exact hf D hDα hDq hDΛ hDζ hseq G.level (by omega) j
      (Finset.mem_filter.mp hj').2.1 _ hρ hρE' t
      (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ1) hc)
  have hcost : ∀ t ∈ Set.Icc tp tf, CycleComparison.Coarse.covPolyConst
      (CycleComparison.Coarse.fbCovConst (liftLength D G.level)
        (covPrimitive D G.level t) (r + N + 2 * p)) p ≤ Ccov := by
    intro t _ht
    exact (hcov Λ (by omega) D hDα hDq hDΛ hDζ hband G.level (by omega) hmterm
      (r + N + 2 * p) p t).trans (le_max_right _ _)
  exact native_liftedFieldW_readout_energy_real_price slotLifts hi hΛ1 hζD hband htorus
    r hres (by have hh := Nat.le_max_left (r + 1) sZ; omega)
    p Naux sX sZ η tp tf Y hk Yw hYw hcompat CcT PZ a u w hfield Yhi heq
    Sbar hSbar hSSbar (weakChartJetBudget_ge_one _ _) hrs hrse hρ hν hB hνB hcell' hflow
    hcr hcr1 (by dsimp [Ccov]; positivity) hcost Broot hBroot hprice

end AVRegularity.Construction.Preservation.FullLift
end
end
end
