-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
public import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
public import AVRegularity.IterationPassage.Passage.Profiles.ClausesStatement
import AVRegularity.IterationPassage.ErrorJets.LiftIdentification
import AVRegularity.CycleComparison.Coarse.Exists.Cell
import AVRegularity.CycleComparison.Reconstruction.ApproxIdentity
import AVRegularity.Proofs.QuietAtlas.PiolaGeom
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Readout.RepresentationEstimates
import Mathlib.Algebra.Order.Star.Real

section
section
/-! **Regularity and periodicity of the passage lift of a classical field**.

For the actual lift coefficients `CcT` of the passage (`IsPassageLift`), the lift
`passageLift D m N H CcT a` at a time `t` equals the glued lift of the native coefficients of the
slot lifts (`nativeStageLiftFamily_coefficients_unique`, `gluedLift_coeff_congr`), so for a
periodic field `a t` of class `C^{P₀+N}` it is periodic and of class `C^r`, `r ≤ P₀`, by
`nativeStageLiftFamily_glued_contDiff` and `nativeStageLiftFamily_glued_periodic`.

Special cases: `a t = 0` (the lift is `0`); an empty family; a time with no observed pulse (the
glued lift is the empty sum). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.IterationPassage.Passage

variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

/-- The passage lift of a periodic `C^{P₀+N}` field is periodic and `C^r`, `r ≤ P₀`. -/
theorem regularLift_contDiff_periodic
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (P₀ : ℕ) (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2)) (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G G.level N H sX sZ CcT)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (t : ℝ)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a t)) (hp : IsZ2Periodic (a t)) :
    ContDiff ℝ (r : ℕ∞) (passageLift D G.level N H CcT a t) ∧
      IsZ2Periodic (passageLift D G.level N H CcT a t) := by
  classical
  have hc : 0 < D.cellScaleSq G.level :=
    EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have hcell (j : ℤ) (hj : ocCutoff D.α D.q D.Λ G.level j t ≠ 0) :
      (D.cellScaleSq G.level)⁻¹ * t ∈
        Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
          ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hj
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩
  have heq : passageLift D G.level N H CcT a t = fun x => gluedLift
      (ocObsPulses D.α D.q D.Λ G.level t t) (fun j => ocCutoff D.α D.q D.Λ G.level j)
      (D.cellScaleSq G.level) (liftLength D G.level) (D.eps G.level)
      (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level)
      N H (nativeStageLiftFamily slotLifts)
      (fun j s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level j))
      (fun j s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s') a t x := by
    funext x
    apply gluedLift_coeff_congr
    intro j hj hcut hh hhh n _hn m α X z v' u
    have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
    exact nativeStageLiftFamily_coefficients_unique slotLifts sX sZ CcT hCcT
      j hjodd hh hhh n m α _ (hcell j hcut) X z v' u
  rw [heq]
  refine ⟨contDiff_pi.mpr fun v => ?_, ?_⟩
  · apply nativeStageLiftFamily_glued_contDiff slotLifts P₀ hreserve r hrP hrQ _
      (fun j hj => (Finset.mem_filter.mp hj).2.1) _ _ _ _ _ hc.ne' a ha _ _ _ _
      (fun j _ hj => hcell j hj) v
    · intro j _ _
      exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
        (D.slotAnchor G.level j)).of_le (by simp)
    · intro j _ _
      exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
        (D.slotAnchor G.level j) t).of_le (by simp)
  · exact nativeStageLiftFamily_glued_periodic slotLifts hi htorus _
      (fun j hj => (Finset.mem_filter.mp hj).2.1) _ _ _ _ hc.ne' a hp
      (fun j _ hj => hcell j hj)

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The exact split of the five profiles**.

Pure algebra on the time slices of the fields: with `S = fieldKernel`, `P = fieldCov`,
`R = fieldReadout`, `T = passageLift`, the five profiles of `passageProfiles` sum to
`F(aU) - 𝖱F'(aY)` in normalized coordinates. The
ingredients are: `R` is a constant continuous linear map applied pointwise (`regularReadoutFull`),
so it is additive and commutes with `P_p` on `C^{2p}` fields (`liftId_covPolyP_clm`); `P_p` is
additive on `C^{2p}` fields; `T` is additive on `C^N` fields at one time (`gluedLift_add_input`);
the normalized readout is the matrix `readoutCLM` (positive masses).

Special cases: `p = 0` (`P_p = I`); `aY t = 0` (four profiles vanish, the fifth is `F(aU)`); an
empty family (all fields take values in the trivial space). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.IterationPassage.Passage

section Cov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `P_p` consumes `2p` derivatives. -/
theorem regularCov_contDiff (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p n : ℕ) {b : Vec 2 → E}
    (hb : ContDiff ℝ ((n + 2 * p : ℕ) : ℕ∞) b) : ContDiff ℝ (n : ℕ∞) (covPolyP Hc p b) := by
  unfold covPolyP
  rw [Finset.sum_fn]
  refine ContDiff.sum fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  refine ContDiff.const_smul _ ?_
  exact AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc l n b
    (hb.of_le (by exact_mod_cast (by omega : n + 2 * l ≤ n + 2 * p)))

/-- `P_p` of a periodic `C^{2p}` field is periodic. -/
theorem regularCov_periodic (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {b : Vec 2 → E}
    (hb : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) b) (hp : IsZ2Periodic b) :
    IsZ2Periodic (covPolyP Hc p b) := by
  intro n x
  simp only [covPolyP, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_periodic Hc l b
    (hb.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p))) hp n x]

/-- `P_p` is additive on `C^{2p}` fields. -/
theorem regularCov_add (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f g : Vec 2 → E}
    (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f) (hg : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) g) :
    covPolyP Hc p (f + g) = covPolyP Hc p f + covPolyP Hc p g := by
  unfold covPolyP
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hf' : ContDiff ℝ ((2 * l : ℕ) : ℕ∞) f := hf.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p))
  have hg' : ContDiff ℝ ((2 * l : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p))
  rw [CycleComparison.Coarse.covLin_iterate_add Hc l hf' hg', smul_add]

end Cov

section Readout

/-- The readout `𝖱` as one continuous linear map of the component fibres. -/
def regularReadoutFull (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp} :
    (∀ v' : CompIn S', ScalarH v'.1.root) →L[ℝ] (∀ v : CompIn S, ScalarH v.1.root) :=
  open scoped Classical in
  ContinuousLinearMap.pi fun v : CompIn S => ∑ v' : CompIn S',
    (if compParent m v'.1 = v.1 then E ^ (η₀ * ((compWord m v'.1).length : ℝ)) else 0) •
      (ContinuousLinearMap.proj v' : (∀ v' : CompIn S', ScalarH v'.1.root) →L[ℝ] ℝ)

theorem regularReadoutFull_apply (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (z : ∀ v' : CompIn S', ScalarH v'.1.root) (v : CompIn S) :
    regularReadoutFull (S := S) m E η₀ z v = ∑ c : CompIn S',
      (if compParent m c.1 = v.1 then E ^ (η₀ * ((compWord m c.1).length : ℝ)) * z c else 0) := by
  classical
  simp only [regularReadoutFull, ContinuousLinearMap.pi_apply]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : compParent m c.1 = v.1 <;> simp [h]

theorem fieldReadout_eq_full (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (a : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ) (x : Vec 2) :
    fieldReadout (S := S) m E η₀ a t x = regularReadoutFull (S := S) m E η₀ (a t x) := by
  classical
  funext v
  rw [regularReadoutFull_apply]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent m v'.1 = v.1 <;> simp [h]

theorem fieldReadout_eq_full_slice (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (a : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ) :
    fieldReadout (S := S) m E η₀ a t = fun x => regularReadoutFull (S := S) m E η₀ (a t x) :=
  funext fun x => fieldReadout_eq_full m E η₀ a t x

theorem regularReadout_contDiff (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (a : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ) {n : ℕ}
    (ha : ContDiff ℝ (n : ℕ∞) (a t)) :
    ContDiff ℝ (n : ℕ∞) (fieldReadout (S := S) m E η₀ a t) := by
  rw [fieldReadout_eq_full_slice]
  exact (regularReadoutFull (S := S) (S' := S') m E η₀).contDiff.comp ha

theorem regularReadout_periodic (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (a : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ) (ha : IsZ2Periodic (a t)) :
    IsZ2Periodic (fieldReadout (S := S) m E η₀ a t) := by
  intro n x
  rw [fieldReadout_eq_full, fieldReadout_eq_full, ha n x]

/-- `P_p` commutes with the constant readout on a `C^{2p}` slice. -/
theorem regularReadout_cov_comm (D : OCData) (m p : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (a : ℝ → Vec 2 → ∀ v' : CompIn S', ScalarH v'.1.root) (t : ℝ)
    (ha : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (a t)) (x : Vec 2) :
    fieldReadout (S := S) m E η₀ (fieldCov D m p a) t x =
      fieldCov D m p (fieldReadout (S := S) m E η₀ a) t x := by
  rw [fieldReadout_eq_full]
  change regularReadoutFull (S := S) m E η₀ (covPolyP (covPrimitive D m t) p (a t) x) =
    covPolyP (covPrimitive D m t) p (fieldReadout (S := S) m E η₀ a t) x
  rw [ErrorJets.liftId_covPolyP_clm _ (regularReadoutFull (S := S) m E η₀) p (a t) ha x,
    fieldReadout_eq_full_slice]

/-- The normalized readout is the matrix `readoutCLM`. -/
theorem regularReadout_normalized (m : ℕ) (E η₀ : ℝ) {S S' : Finset Comp}
    (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hπ' : ∀ v', 0 < π' v')
    (z : ∀ v' : CompIn S', ScalarH v'.1.root) :
    readoutCLM m E η₀ π π' (toCompSpace π' z) =
      toCompSpace π (regularReadoutFull (S := S) m E η₀ z) := by
  classical
  ext v
  change (∑ c : CompIn S', readoutMatrix m E η₀ π π' v c *
      ((Real.sqrt (π' c))⁻¹ * z c)) = (Real.sqrt (π v))⁻¹ * _
  rw [regularReadoutFull_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  dsimp only [readoutMatrix]
  by_cases h : compParent m c.1 = v.1
  · simp only [h, ite_true]
    have hn : Real.sqrt (π' c) ≠ 0 := (Real.sqrt_pos.mpr (hπ' c)).ne'
    calc _ = ((Real.sqrt (π v))⁻¹ * E ^ (η₀ * ((compWord m c.1).length : ℝ)) * z c) *
          (Real.sqrt (π' c) * (Real.sqrt (π' c))⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn, mul_one, mul_assoc]
  · simp [h]

theorem toCompSpace_add {S : Finset Comp} (π : CompIn S → ℝ) (z w : ∀ v : CompIn S, ScalarH v.1.root) :
    toCompSpace π (z + w) = toCompSpace π z + toCompSpace π w := by
  ext v
  simp [toCompSpace, mul_add]

theorem toCompSpace_sub {S : Finset Comp} (π : CompIn S → ℝ) (z w : ∀ v : CompIn S, ScalarH v.1.root) :
    toCompSpace π (z - w) = toCompSpace π z - toCompSpace π w := by
  ext v
  simp [toCompSpace, mul_sub]

end Readout

section Lift

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The lift at the time `t` only sees the field at the time `t`. -/
theorem regularLift_congr_time (m N depth : ℕ) {S : Finset Comp}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn S) (fun v => ScalarH v.1.root))
    (hc : D.cellScaleSq m ≠ 0) {a a' : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root} {t : ℝ}
    (h : a t = a' t) : passageLift D m N depth CcT a t = passageLift D m N depth CcT a' t := by
  funext x
  exact CycleComparison.Reconstruction.gluedLift_congr_time _ _ hc _ _ _ _ _ _ _ _ h x

/-- The lift is additive on fields of class `C^N` at the time `t`. -/
theorem regularLift_add (m N depth : ℕ) {S : Finset Comp}
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn S) (fun v => ScalarH v.1.root))
    (hc : D.cellScaleSq m ≠ 0) {a a' : ℝ → Vec 2 → ∀ v : CompIn S, ScalarH v.1.root} {t : ℝ}
    (ha : ContDiff ℝ (N : ℕ∞) (a t)) (ha' : ContDiff ℝ (N : ℕ∞) (a' t)) (x : Vec 2) :
    passageLift D m N depth CcT (fun s y => a s y + a' s y) t x =
      passageLift D m N depth CcT a t x + passageLift D m N depth CcT a' t x :=
  CycleComparison.Reconstruction.gluedLift_add_input _ _ hc _ _ _ _ _ _ _ _
    (fun k _ => Providers.QuietAtlas.flowOf_contDiff D (m - 1) t (D.slotAnchor m k)) a a' ha ha' x

end Lift

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The readout is bounded in the weighted norm** (the `D_E` step of the discarded profiles).

`discCoarse_readout_weightedNorm_le`: for a family `w` of `H^K` carriers with classical
representatives `f_v`, `‖𝖱 w‖_{ρ,K;π} ≤ ‖readoutCLM‖ ‖w‖_{ρ,K;π'}`, where `𝖱 w = succReadout m E η₀ K w`.
The proof: both weighted norms are the classical factorial densities of the normalized fields
(`classicalRep_factorial_energy_eq`), and the normalized readout is the constant map `readoutCLM`
(`regularReadout_normalized`).

Special cases: `w = 0`; `K = 0`; a single component. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage
open AVRegularity.Construction.Preservation.FullLift

theorem discCoarse_weightedNorm_sq {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (ρ : ℝ) {k : ℕ} (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root)) :
    weightedNorm ρ π (fun _ => 1) X ^ 2 = ∑ v, (π v)⁻¹ * factorialNormSq ρ (X v).val := by
  have hmass : 0 ≤ massNormSq (E := fun v : CompIn S => ScalarH v.1.root)
      (K := fun _ => k) ρ (fun v => π v / (fun _ : CompIn S => (1 : ℝ)) v ^ 2)
      (fun v => (X v).val) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.mpr (by simp [(hπ v).le]))
      (factorialNormSq_nonneg ρ _)
  rw [weightedNorm, Real.sq_sqrt hmass, massNormSq]
  simp

/-- The weighted norm squared of a family of classical representatives is the classical factorial
density of the normalized field. -/
theorem discCoarse_weightedNorm_energy {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (ρ : ℝ) {k : ℕ} (X : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root))
    (u : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root)
    (hu : ∀ v, IsClassicalRep (X v) (fun x => u x v) k) :
    ENNReal.ofReal (weightedNorm ρ π (fun _ => 1) X ^ 2) =
      classicalFactorialSq ρ k (compField π u) := by
  rw [discCoarse_weightedNorm_sq π hπ, ENNReal.ofReal_sum_of_nonneg
    (fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le) (factorialNormSq_nonneg ρ _)),
    ← discCoarse_energy_compField π hπ ρ k u (fun v => (hu v).2.1)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le), classicalRep_factorial_energy_eq ρ (X v) _ (hu v)]

/-- The classical representative of the readout carrier. -/
theorem discCoarse_succReadout_rep {S S' : Finset Comp} (m : ℕ) (E η₀ : ℝ) {k : ℕ}
    (w : ∀ v : CompIn S', TorusHk k (ScalarH v.1.root)) (f : Vec 2 → ∀ v : CompIn S', ScalarH v.1.root)
    (hrep : ∀ v, IsClassicalRep (w v) (fun x => f x v) k) (v : CompIn S) :
    IsClassicalRep (succReadout m E η₀ k w v)
      (fun x => regularReadoutFull (S := S) m E η₀ (f x) v) k := by
  have h := readout_classicalRep (hr := ScalarH) le_rfl m E η₀ w (fun c x => f x c) hrep v
  convert h using 2
  rw [regularReadoutFull_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : compParent m c.1 = v.1 <;> simp [hc]

theorem discCoarse_readout_weightedNorm_le {S S' : Finset Comp} (m : ℕ) (E η₀ : ℝ)
    (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hπ : ∀ v, 0 < π v) (hπ' : ∀ v, 0 < π' v)
    (ρ : ℝ) {k : ℕ} (w : ∀ v : CompIn S', TorusHk k (ScalarH v.1.root))
    (f : Vec 2 → ∀ v : CompIn S', ScalarH v.1.root)
    (hrep : ∀ v, IsClassicalRep (w v) (fun x => f x v) k) :
    weightedNorm ρ π (fun _ => 1) (succReadout m E η₀ k w) ≤
      ‖readoutCLM m E η₀ π π'‖ * weightedNorm ρ π' (fun _ => 1) w := by
  set L := readoutCLM m E η₀ π π' with hL
  have h1 := discCoarse_weightedNorm_energy π hπ ρ (succReadout m E η₀ k w)
    (fun x => regularReadoutFull (S := S) m E η₀ (f x)) (discCoarse_succReadout_rep m E η₀ w f hrep)
  have h2 := discCoarse_weightedNorm_energy π' hπ' ρ w f hrep
  have h3 : compField π (fun x => regularReadoutFull (S := S) m E η₀ (f x)) =
      fun x => L (compField π' f x) := by
    funext x
    exact (regularReadout_normalized m E η₀ π π' hπ' (f x)).symm
  have hC : ContDiff ℝ (k : ℕ∞) (compField π' f) :=
    discCoarse_contDiff_compField π' f fun v => (hrep v).2.1
  have h4 := discCoarse_energy_clm_le L ρ k hC
  rw [h3] at h1
  have h5 : ENNReal.ofReal (weightedNorm ρ π (fun _ => 1) (succReadout m E η₀ k w) ^ 2) ≤
      ENNReal.ofReal ((‖L‖ * weightedNorm ρ π' (fun _ => 1) w) ^ 2) := by
    rw [h1, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), h2]
    exact h4
  have h6 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 h5
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).1 h6

end AVRegularity.IterationPassage.Passage
end
end
end

section
section
/-! **The profile proposition at the data of one passage**.

`passageClauses_at_data`: `PassageClauses` for a pair of families `U(t)`, `Y(t)` on the window
`[t_p, t_f]` from

* the five profile facts for arbitrary classical fields at the times `t ∈ [s₀, t_f]` (the data
  parts of the five profile statements, instantiated; `hreg`, `hcov`, `hlift`, `hdisc`, `herr`,
  the last four with one constant `C₁ ≥ 0`);
* `SmoothRepOfHigherStatement`;
* for every time of the window a lift of `U(t)` of order `K + N + 2p + 4` (the molecular buffer)
  and a lift of `Y(t)` of order `N_aux` with marked weighted norm `≤ C_r A` at the radius `rhoEnh`
  (the regenerated solution);
* the jets `PassageJetClauses` with the constant `C_j` (`passage_error_jets`);
* the readout norm `‖𝖱‖ ≤ 1 + C_n E^{5η₀/4}`.

Then `PassageClauses` holds with every `C ≥ max{C_n, C₁, C₁C_r + C₁C_j}`. The error profile is
`𝓘_{e,K;s}(𝓔) ≤ C₁E^{-qZ}·C_jE^{Q/2}A ≤ C₁C_jE^PA` since `P + qZ ≤ Q/2` and `0 < E ≤ 1`.

Special cases: `A = 0` (all lifts vanish, the bounds are `0 ≤ 0`); an empty family. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The fifth profile is the error `F(aU - TP_p𝖱aY)`; its regularity from `ProfilesRegular`. -/
theorem profilesRegular_fifth (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth K : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ)
    (h : ProfilesRegular D law G Gr m p N depth K η₀ φ₀ Sr CcT aU aY t) :
    ContDiff ℝ (K : ℕ) (compField (G.mass law) (fun x v => aU t x v - passageLift D m N depth CcT
        (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ aY)) t x v)) ∧
      IsZ2Periodic (compField (G.mass law) (fun x v => aU t x v - passageLift D m N depth CcT
        (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ aY)) t x v)) :=
  h (_, D.eps m) (by
    simp only [passageProfiles, List.mem_cons, List.mem_nil_iff, or_false]
    exact Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- **The profile proposition at the data of one passage.** -/
theorem passageClauses_at_data (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K Naux : ℕ) (s η₀ mu wexp P Q qZ c₀ cr Cn Cr Cj C₁ C A s₀ tp tf : ℝ)
    (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (hs₀ : 0 < s) (hs₁ : s < 1) (he : 0 < D.eps m) (heE : D.eps m ≤ D.eps (m - 1))
    (hE1 : D.eps (m - 1) ≤ 1) (hA : 0 ≤ A) (hNaux : K + N + 2 * p + 4 ≤ Naux) (hstp : s₀ ≤ tp)
    (hQ : P + qZ ≤ Q / 2) (hC₁ : 0 ≤ C₁) (hCr : 0 ≤ Cr) (hCj : 0 ≤ Cj) (hCn : Cn ≤ C)
    (hC₁C : C₁ ≤ C) (hCC : C₁ * Cr + C₁ * Cj ≤ C)
    (hsm : SmoothRepOfHigherStatement)
    (hRn : ‖readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law)‖ ≤
      1 + Cn * D.eps (m - 1) ^ (5 * η₀ / 4))
    (hUn : ∀ t ∈ Set.Icc tp tf, ∃ Un : ∀ v : CompIn G.comps,
      TorusHk (K + N + 2 * p + 4) (ScalarH v.1.root),
      ∀ v, truncateTorusHk (Nat.zero_le _) (Un v) = U v t)
    (hYn : ∀ t ∈ Set.Icc tp tf, ∃ Yn : ∀ v : CompIn Gr.comps, TorusHk Naux (ScalarH v.1.root),
      (∀ v, truncateTorusHk (Nat.zero_le _) (Yn v) = Y v t) ∧
      weightedNorm (rhoEnh D cr m) (Gr.mass law) (Gr.marker law) Yn ≤ Cr * A)
    (hjet : ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) →
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2)) →
      ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
        IsPassageLift G m N depth sX sZ CcT →
        PassageJetClauses law G Gr m p N depth K η₀ Q Cj c₀ A tp tf CcT aU aY)
    (hreg : ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N depth sX sZ CcT →
      ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ),
        s₀ ≤ t → t ≤ tf →
        ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aU t) → IsZ2Periodic (aU t) →
        ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
        ProfilesRegular D law G Gr m p N depth K η₀ φ₀ Sr CcT aU aY t ∧
        ProfilesSplit D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY t)
    (hcov : ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N depth sX sZ CcT →
      ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ),
        s₀ ≤ t → t ≤ tf →
        ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
        profileNorm (D.eps (m - 1)) K s
            (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => q.1 t).getD 0 0) ≤
          ENNReal.ofReal (C₁ * D.eps (m - 1) ^ wexp) *
            profileSeminorm (D.eps (m - 1)) K s (compField (Gr.mass law) (aY t)))
    (hlift : ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N depth sX sZ CcT →
      ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ),
        s₀ ≤ t → t ≤ tf →
        ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
        profileNorm (D.eps m) K s
            (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => q.1 t).getD 1 0) ≤
          ENNReal.ofReal (C₁ * D.eps (m - 1) ^ mu) *
            profileSeminorm (D.eps (m - 1)) K s (compField (Gr.mass law) (aY t)))
    (hdisc : ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N depth sX sZ CcT →
      ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ),
        s₀ ≤ t → t ≤ tf →
        ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
      ∀ (Yn : ∀ v : CompIn Gr.comps, TorusHk Naux (ScalarH v.1.root)) (B : ℝ),
        (∀ v, (Yn v).toFunction.jet (valueIndex2 Naux) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => aY t x v) →
        weightedNorm (rhoEnh D cr m) (Gr.mass law) (Gr.marker law) Yn ≤ B →
        profileNorm (D.eps (m - 1)) K s
            (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => q.1 t).getD 2 0) +
          profileNorm (D.eps m) K s
            (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => q.1 t).getD 3 0) ≤
          ENNReal.ofReal (C₁ * D.eps (m - 1) ^ P * B))
    (herr : ∀ (g : Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (t : ℝ), s₀ ≤ t → t ≤ tf →
      ContDiff ℝ (K : ℕ) (compField (G.mass law) g) → IsZ2Periodic (compField (G.mass law) g) →
      ∀ (En : ∀ v : CompIn G.comps, TorusHk (K + 2) (ScalarH v.1.root)) (B : ℝ),
        (∀ v, (En v).toFunction.jet (valueIndex2 (K + 2)) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => g x v) →
        weightedNorm (rhoStar D c₀ m) (G.mass law) (fun _ => 1) En ≤ B →
        profileNorm (D.eps m) K s (compField (G.mass law) g) ≤
          ENNReal.ofReal (C₁ * D.eps (m - 1) ^ (-qZ) * B)) :
    PassageClauses D law G Gr m p N depth sX sZ K s η₀ mu wexp P C A tp tf φ₀ Sr U Y := by
  classical
  have hE0 : 0 < D.eps (m - 1) := he.trans_le heE
  have hC0 : 0 ≤ C := hC₁.trans hC₁C
  have hsmooth : ∃ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) ∧
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2)) := by
    have hU : ∀ t, ∃ a : Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root,
        t ∈ Set.Icc tp tf → IsSmoothRep (fun v => U v t) a (K + N + 2 * p + 2) := by
      intro t
      by_cases ht : t ∈ Set.Icc tp tf
      · obtain ⟨Un, hUn'⟩ := hUn t ht
        obtain ⟨a, ha⟩ := hsm (K + N + 2 * p + 2) (K + N + 2 * p + 4) le_rfl (fun v => U v t) Un
          hUn'
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => absurd h ht⟩
    have hY : ∀ t, ∃ a : Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root,
        t ∈ Set.Icc tp tf → IsSmoothRep (fun v => Y v t) a (K + N + 2 * p + 2) := by
      intro t
      by_cases ht : t ∈ Set.Icc tp tf
      · obtain ⟨Yn, hYn', -⟩ := hYn t ht
        obtain ⟨a, ha⟩ := hsm (K + N + 2 * p + 2) Naux hNaux (fun v => Y v t) Yn hYn'
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => absurd h ht⟩
    choose aU haU using hU
    choose aY haY using hY
    exact ⟨aU, aY, fun t ht => haU t ht, fun t ht => haY t ht⟩
  refine passageClauses_of_parts law G Gr m p N depth sX sZ K s η₀ mu wexp P C A tp tf φ₀ Sr U Y
    hs₀ hs₁ he heE hC0
    (hRn.trans (by
      have := mul_le_mul_of_nonneg_right hCn (Real.rpow_nonneg hE0.le (5 * η₀ / 4))
      linarith))
    hsmooth ?_
  intro aU aY haU haY CcT hCcT t ht
  have hst : s₀ ≤ t := hstp.trans ht.1
  obtain ⟨hR, hS⟩ := hreg CcT hCcT aU aY t hst ht.2 (haU t ht).1 (haU t ht).2.1 (haY t ht).1
    (haY t ht).2.1
  have hw : 0 ≤ D.eps (m - 1) ^ wexp := Real.rpow_nonneg hE0.le _
  have hm : 0 ≤ D.eps (m - 1) ^ mu := Real.rpow_nonneg hE0.le _
  have hP : 0 ≤ D.eps (m - 1) ^ P := Real.rpow_nonneg hE0.le _
  refine ⟨hR, hS, ⟨?_, ?_⟩, ?_⟩
  · exact (hcov CcT hCcT aU aY t hst ht.2 (haY t ht).1 (haY t ht).2.1).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC₁C hw)) le_rfl)
  · exact (hlift CcT hCcT aU aY t hst ht.2 (haY t ht).1 (haY t ht).2.1).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC₁C hm)) le_rfl)
  · obtain ⟨Yn, hYn', hYb⟩ := hYn t ht
    have hlink : ∀ v, (Yn v).toFunction.jet (valueIndex2 Naux)
        =ᵐ[volume.restrict AVenhance.unitCube] fun x => aY t x v := by
      intro v
      have h1 := IterationPassage.torus_truncate_value_ae (Nat.zero_le Naux) (Yn v)
      rw [hYn' v] at h1
      exact h1.symm.trans ((haY t ht).2.2 v)
    have hD := hdisc CcT hCcT aU aY t hst ht.2 (haY t ht).1 (haY t ht).2.1 Yn (Cr * A) hlink hYb
    obtain ⟨-, En, hEn, hEb⟩ := hjet aU aY haU haY CcT hCcT t ht
    obtain ⟨h5c, h5p⟩ := profilesRegular_fifth law G Gr m p N depth K η₀ φ₀ Sr CcT aU aY t hR
    have hErr := herr _ t hst ht.2 h5c h5p En _ hEn hEb
    have hpow : D.eps (m - 1) ^ (-qZ) * D.eps (m - 1) ^ (Q / 2) ≤ D.eps (m - 1) ^ P := by
      rw [← Real.rpow_add hE0]
      exact Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (by linarith)
    have hq : 0 ≤ D.eps (m - 1) ^ (-qZ) := Real.rpow_nonneg hE0.le _
    have hQ2 : 0 ≤ D.eps (m - 1) ^ (Q / 2) := Real.rpow_nonneg hE0.le _
    have ha : 0 ≤ C₁ * D.eps (m - 1) ^ P * (Cr * A) :=
      mul_nonneg (mul_nonneg hC₁ hP) (mul_nonneg hCr hA)
    have hb : 0 ≤ C₁ * D.eps (m - 1) ^ (-qZ) * (Cj * D.eps (m - 1) ^ (Q / 2) * A) :=
      mul_nonneg (mul_nonneg hC₁ hq) (mul_nonneg (mul_nonneg hCj hQ2) hA)
    have hsum : C₁ * D.eps (m - 1) ^ P * (Cr * A) +
        C₁ * D.eps (m - 1) ^ (-qZ) * (Cj * D.eps (m - 1) ^ (Q / 2) * A) ≤
          C * D.eps (m - 1) ^ P * A := by
      have h1 : C₁ * D.eps (m - 1) ^ (-qZ) * (Cj * D.eps (m - 1) ^ (Q / 2) * A) ≤
          C₁ * Cj * D.eps (m - 1) ^ P * A := by
        have := mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hC₁ hCj) hA)
        linarith
      have h2 := mul_le_mul_of_nonneg_right hCC (mul_nonneg hP hA)
      linarith
    show _ + _ + profileNorm (D.eps m) K s (compField (G.mass law) fun x v => aU t x v -
      passageLift D m N depth CcT (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ aY)) t x v) ≤ _
    exact (add_le_add hD hErr).trans
      ((ENNReal.ofReal_add ha hb).symm.le.trans (ENNReal.ofReal_le_ofReal hsum))

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **Scaled Sobolev to profile**: `sobolevProfile : SobolevProfileStatement`.

Route: `sobolevProfile_coord` (the coordinates of `∂^α (compField π g)` are
`π_v^{-1/2} ∂^α g_v`), `sobolevProfile_component_sq` (the scaled sup bound for each component),
the `ℓ²(π⁻¹)` sum of the squares is `weightedNorm²`, and the packing of the profile norm
(amplitude plus at most `(K+1)²` multi-indices, each term at most `Y`). -/

@[expose] public noncomputable section

namespace AVRegularity.IterationPassage.Passage

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity AVenhance
open scoped ENNReal

/-- The `v`-th coordinate of `∂^α (compField π g)` is `π_v^{-1/2} ∂^α g_v`. -/
theorem sobolevProfile_coord {S : Finset Comp} (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (g : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root) {K : ℕ}
    (hC : ContDiff ℝ (K : ℕ) (compField π g)) (α : Fin 2 → ℕ) (hα : α 0 + α 1 ≤ K)
    (x : Vec 2) (v : CompIn S) :
    (partialDerivative α (compField π g) x).ofLp v =
      (Real.sqrt (π v))⁻¹ * partialDerivative α (fun y => g y v) x := by
  have hs : 0 < Real.sqrt (π v) := Real.sqrt_pos.mpr (hπ v)
  let R : CompSpace S →L[ℝ] ℝ := (Real.sqrt (π v)) • PiLp.proj 2 (fun _ : CompIn S => ℝ) v
  have hR : (fun y => g y v) = fun y => R (compField π g y) := by
    funext y
    simp only [R, compField, toCompSpace, smul_apply, PiLp.proj_apply,
      smul_eq_mul]
    field_simp
  have h := Readout.partialDerivative_comp α hα R (compField π g) hC
  have h2 := congrFun h x
  rw [← hR] at h2
  rw [h2]
  simp only [R, smul_apply, PiLp.proj_apply, smul_eq_mul]
  field_simp

theorem sobolevProfile_rpow {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    ρ ^ (-(j : ℝ) - 1) = (ρ ^ (j + 1))⁻¹ := by
  rw [show -(j : ℝ) - 1 = -((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hρ.le,
    Real.rpow_natCast]

theorem sobolevProfile_supNorm_le {S : Finset Comp} (G : Vec 2 → CompSpace S) (B : ℝ)
    (h : ∀ x, ‖G x‖ ≤ B) : supNorm G ≤ ENNReal.ofReal B := by
  unfold supNorm
  refine iSup_le fun x => ?_
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  exact ENNReal.ofReal_le_ofReal (h x)

theorem sobolevProfile_one_le_factorial (α : Fin 2 → ℕ) : 1 ≤ multiIndexFactorial α := by
  unfold multiIndexFactorial
  rw [Fin.prod_univ_two]
  have h0 : (1 : ℝ) ≤ (α 0).factorial := by exact_mod_cast Nat.factorial_pos _
  have h1 : (1 : ℝ) ≤ (α 1).factorial := by exact_mod_cast Nat.factorial_pos _
  exact one_le_mul_of_one_le_of_one_le h0 h1

theorem sobolevProfile_card_le (K : ℕ) : (multiIndicesBetween 1 K).card ≤ (K + 1) ^ 2 := by
  unfold multiIndicesBetween
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const, sq]

/-- **Scaled Sobolev to profile.** -/
theorem sobolevProfile : SobolevProfileStatement := by
  intro K
  refine ⟨(((K + 1) ^ 2 + 1 : ℕ) : ℝ) * Real.sqrt (sobolevScaledConst (K + 2)),
    by positivity, ?_⟩
  intro S π hπ ρ lam s hρ hρ1 hlam X g hC hper hX
  set W : ℝ := weightedNorm ρ π (fun _ => 1) X with hW
  set sq : ℝ := Real.sqrt (sobolevScaledConst (K + 2)) with hsq
  set T : ℝ := ∑ j ∈ Finset.range (K + 1), lam ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1) with hT
  have hCs : 0 ≤ sobolevScaledConst (K + 2) := by unfold sobolevScaledConst; positivity
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hmass : 0 ≤ massNormSq (E := fun v : CompIn S => ScalarH v.1.root)
      (K := fun _ => K + 2) ρ (fun v => π v / (fun _ : CompIn S => (1 : ℝ)) v ^ 2)
      (fun v => (X v).val) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.mpr (by simp [(hπ v).le]))
      (factorialNormSq_nonneg ρ _)
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hW2 : W ^ 2 = ∑ v : CompIn S, (π v)⁻¹ * factorialNormSq ρ (X v).val := by
    rw [hW, weightedNorm, Real.sq_sqrt hmass, massNormSq]
    simp
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (by positivity)
  -- the sup bound of one derivative
  have key : ∀ α : Fin 2 → ℕ, α 0 + α 1 ≤ K → ∀ x : Vec 2,
      ‖partialDerivative α (compField π g) x‖ ≤ sq * (ρ ^ (α 0 + α 1 + 1))⁻¹ * W := by
    intro α hα x
    have hcomp : ∀ v : CompIn S, (partialDerivative α (fun y => g y v) x) ^ 2 ≤
        sobolevScaledConst (K + 2) * (ρ ^ (2 * (α 0 + α 1) + 2))⁻¹ *
          factorialNormSq ρ (X v).val := by
      intro v
      have hs : 0 < Real.sqrt (π v) := Real.sqrt_pos.mpr (hπ v)
      let R : CompSpace S →L[ℝ] ℝ := (Real.sqrt (π v)) • PiLp.proj 2 (fun _ : CompIn S => ℝ) v
      have hR : (fun y => g y v) = fun y => R (compField π g y) := by
        funext y
        simp only [R, compField, toCompSpace, smul_apply, PiLp.proj_apply,
          smul_eq_mul]
        field_simp
      have hcv : ContDiff ℝ (K : ℕ) (fun y => g y v) := by
        rw [hR]; exact R.contDiff.comp hC
      have hpv : IsZ2Periodic (fun y => g y v) := by
        intro n y
        rw [hR]
        simp only
        rw [hper n y]
      exact sobolevProfile_component_sq (X v) (fun y => g y v) hcv hpv (hX v) α hα hρ hρ1 x
    have hsum : ‖partialDerivative α (compField π g) x‖ ^ 2 ≤
        sobolevScaledConst (K + 2) * (ρ ^ (2 * (α 0 + α 1) + 2))⁻¹ * W ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, hW2, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _
      rw [Real.norm_eq_abs, sq_abs, sobolevProfile_coord π hπ g hC α hα x v, mul_pow, inv_pow,
        Real.sq_sqrt (hπ v).le]
      have := hcomp v
      have hpv : 0 ≤ (π v)⁻¹ := inv_nonneg.mpr (hπ v).le
      nlinarith [mul_le_mul_of_nonneg_left this hpv]
    have hB : (sq * (ρ ^ (α 0 + α 1 + 1))⁻¹ * W) ^ 2 =
        sobolevScaledConst (K + 2) * (ρ ^ (2 * (α 0 + α 1) + 2))⁻¹ * W ^ 2 := by
      rw [mul_pow, mul_pow, hsq, Real.sq_sqrt hCs, inv_pow, ← pow_mul]
      congr 3
      ring
    have hB0 : 0 ≤ sq * (ρ ^ (α 0 + α 1 + 1))⁻¹ * W := by positivity
    exact (sq_le_sq₀ (norm_nonneg _) hB0).mp (hB ▸ hsum)
  -- one term of the profile norm
  have term : ∀ α : Fin 2 → ℕ, α 0 + α 1 ≤ K →
      ENNReal.ofReal (lam ^ (((α 0 + α 1 : ℕ) : ℝ) - s)) * supNorm (partialDerivative α (compField π g)) ≤
        ENNReal.ofReal (sq * T * W) := by
    intro α hα
    set j := α 0 + α 1 with hj
    have hsup := sobolevProfile_supNorm_le _ _ (key α hα)
    refine (mul_le_mul' le_rfl hsup).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hterm : lam ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1) ≤ T :=
      Finset.single_le_sum (f := fun j : ℕ => lam ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1))
        (fun j _ => by positivity) (Finset.mem_range.mpr (by omega))
    rw [sobolevProfile_rpow hρ] at hterm
    have hl : 0 ≤ lam ^ ((j : ℝ) - s) := by positivity
    calc lam ^ ((j : ℝ) - s) * (sq * (ρ ^ (j + 1))⁻¹ * W)
        = sq * (lam ^ ((j : ℝ) - s) * (ρ ^ (j + 1))⁻¹) * W := by ring
      _ ≤ sq * T * W := by gcongr
  have hamp : ENNReal.ofReal (lam ^ (-s)) * supNorm (compField π g) ≤ ENNReal.ofReal (sq * T * W) := by
    have h0 : partialDerivative (0 : Fin 2 → ℕ) (compField π g) = compField π g := rfl
    have := term 0 (Nat.zero_le _)
    rw [h0] at this
    simpa using this
  have hsemi : ∀ α ∈ multiIndicesBetween 1 K,
      ENNReal.ofReal (lam ^ (((α 0 + α 1 : ℕ) : ℝ) - s) / multiIndexFactorial α) *
        supNorm (partialDerivative α (compField π g)) ≤ ENNReal.ofReal (sq * T * W) := by
    intro α hαm
    have hα : α 0 + α 1 ≤ K := by
      simp only [multiIndicesBetween, Finset.mem_filter] at hαm
      exact hαm.2.2
    refine le_trans (mul_le_mul' ?_ le_rfl) (term α hα)
    exact ENNReal.ofReal_le_ofReal (div_le_self (by positivity)
      (sobolevProfile_one_le_factorial α))
  unfold profileNorm profileSeminorm
  have hsumle : ∑ α ∈ multiIndicesBetween 1 K,
      ENNReal.ofReal (lam ^ (((α 0 + α 1 : ℕ) : ℝ) - s) / multiIndexFactorial α) *
        supNorm (partialDerivative α (compField π g)) ≤
      ((multiIndicesBetween 1 K).card : ℝ≥0∞) * ENNReal.ofReal (sq * T * W) := by
    calc _ ≤ ∑ _α ∈ multiIndicesBetween 1 K, ENNReal.ofReal (sq * T * W) :=
          Finset.sum_le_sum hsemi
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((multiIndicesBetween 1 K).card : ℝ≥0∞) ≤ (((K + 1) ^ 2 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast sobolevProfile_card_le K
  calc _ ≤ ENNReal.ofReal (sq * T * W) +
        (((K + 1) ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (sq * T * W) :=
        add_le_add hamp (hsumle.trans (mul_le_mul' hcard le_rfl))
    _ = (((K + 1) ^ 2 + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (sq * T * W) := by
        push_cast
        ring
    _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end AVRegularity.IterationPassage.Passage
end
end
end

section
section
/-! **The profile proposition of one passage from its six ingredients**.

`passageProfileClauses_of_ingredients`: `PassageProfileClausesStatement` from
`SmoothRepOfHigherStatement` and the five prefix statements `PassageProfilesRegularStatement`,
`PassageRetainedCovarianceStatement`, `PassageRetainedLiftStatement`,
`PassageDiscardedProfilesStatement` and `PassageErrorProfileStatement`.

Quantifier alignment: the five statements have the same prefix; `Λ₀`, lift floors, `Kneed`,
carrier constants, ledger thresholds and `m_*` by maxima, `c₀max` by minima, thresholds by
`certificateThresholdJoin`. The readout norm `‖𝖱‖ ≤ 1 + C_nE^{5η₀/4} ≤ 1 + |C_n|` (`0 < E ≤ 1`,
`η₀ > 0`) feeds the three statements that ask a bound of the norm. With `C₁ = |C_c| + |C_l| +
|C_d| + |C_e|` the constant is `C₀ = |C_n| + C₁ + C₁C_r + C₁C_j`. The data step is
`passageClauses_at_data`; `K + N + 2p + 4 ≤ N_aux` is `IsPassageOrders` and `P + qZ_K ≤ Q/2` is the
schedule. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly

namespace AVRegularity.IterationPassage.Passage

/-- The wavelengths decrease. -/
theorem eps_le_pred (D : OCData) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (m : ℕ) :
    D.eps m ≤ D.eps (m - 1) := by
  cases m with
  | zero => exact le_rfl
  | succ n => exact CycleReference.epsilon_succ_le hq hΛ

/-- The data part of `PassageProfileClausesStatement` from the data parts of its ingredients. -/
theorem passageProfileClausesData_of_parts {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {bw : ℝ} {K : ℕ} {Pacc Q T₀ : ℝ} {r₀ D₀ : ℕ} {τe : ℝ}
    {H J N p nk Naux npad : ℕ} {σ₀ : ℝ} {sX sZ : ℕ} {Ce : ℝ} {kS kI : InvConsts} {CI Cw : ℝ}
    {j₀ : ℕ} (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hs₀ : 0 < s) (hs₁ : s < 1)
    (hη : 0 ≤ succEta0 α q s) (hNaux : K + N + 2 * p + 4 ≤ Naux)
    (hQ : Pacc + q * iterZ α q s K ≤ Q / 2) (Cn Cr Cj C₁ C : ℝ) (mr mc ml md me mStar : ℕ)
    (hmr : mr ≤ mStar) (hmc : mc ≤ mStar) (hml : ml ≤ mStar) (hmd : md ≤ mStar)
    (hme : me ≤ mStar) (hC₁ : 0 ≤ C₁) (hCr : 0 ≤ Cr) (hCj : 0 ≤ Cj) (hCn : Cn ≤ C)
    (hC₁C : C₁ ≤ C) (hCC : C₁ * Cr + C₁ * Cj ≤ C) (hsm : SmoothRepOfHigherStatement)
    (hr : PassageProfilesRegularData α s q ζ Λ φ₀ hφ₀ bw K T₀ r₀ D₀ τe H J N p nk npad σ₀ sX sZ Ce
      kS kI CI Cw j₀ mr)
    (hc : PassageRetainedCovarianceData α s q ζ Λ φ₀ hφ₀ bw K T₀ r₀ D₀ τe H J N p nk npad σ₀ sX sZ
      Ce kS kI CI Cw j₀ (1 + |Cn|) C₁ mc)
    (hl : PassageRetainedLiftData α s q ζ Λ φ₀ hφ₀ bw K T₀ r₀ D₀ τe H J N p nk npad σ₀ sX sZ Ce kS
      kI CI Cw j₀ (1 + |Cn|) C₁ ml)
    (hd : PassageDiscardedProfilesData α s q ζ Λ φ₀ hφ₀ bw K Pacc T₀ r₀ D₀ τe H J N p nk Naux npad
      σ₀ sX sZ Ce kS kI CI Cw j₀ (1 + |Cn|) C₁ md)
    (he : PassageErrorProfileData α s q ζ Λ φ₀ hφ₀ bw K T₀ r₀ D₀ τe H J N p nk npad σ₀ sX sZ Ce kS
      kI CI Cw j₀ C₁ me) :
    PassageProfileClausesData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux npad σ₀ sX
      sZ Ce kS kI CI Cw j₀ Cn Cr Cj C mStar := by
  intro D hα hq' hΛ' hζ
  subst hα hq' hΛ' hζ
  intro hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hgen hmol m hm hmn hnM
    tA s₀ htA hs₀' hwin hT G G' hcas hlev hinv hsucc tp A hstp hA U Y hRn hUn hYn hjet
  have hE := Scales.epsilon_basic (m := m - 1) hq.1 hΛ
  have hE0 : 0 < D.eps (m - 1) := hE.1
  have hE1 : D.eps (m - 1) ≤ 1 := hE.2.1
  have he0 : 0 < D.eps m := (Scales.epsilon_basic (m := m) hq.1 hΛ).1
  have hRn' : ‖readoutCLM m (D.eps (m - 1)) (succEta0 D.α D.q s) (G.mass law)
      ((G'.retained m H J).mass law)‖ ≤ 1 + |Cn| := by
    refine hRn.trans ?_
    have h1 : D.eps (m - 1) ^ (5 * succEta0 D.α D.q s / 4) ≤ 1 :=
      Real.rpow_le_one hE0.le hE1 (by linarith)
    have h2 := mul_le_mul (le_abs_self Cn) h1 (Real.rpow_nonneg hE0.le _) (abs_nonneg Cn)
    linarith
  exact passageClauses_at_data law G (G'.retained m H J) m p N (succSchedR r₀ J H) sX sZ K Naux s
    (succEta0 D.α D.q s) (ocMuS D.α D.q s) (ocDelta D.α D.q - 2 * σ₀) Pacc Q
    (D.q * iterZ D.α D.q s K) kI.c₀ kI.cr Cn Cr Cj C₁ C A s₀ tp tf φ₀ (freshK (m - 1)) U Y hs₀ hs₁
    he0 (eps_le_pred D hq.1 hΛ m) hE1 hA hNaux hstp hQ hC₁ hCr hCj hCn hC₁C hCC hsm hRn hUn hYn hjet
    (hr D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hgen
      hmol m (hmr.trans hm) hmn hnM tA s₀ htA hs₀' hwin hT G G' hcas hlev hinv hsucc)
    (hc D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hgen
      hmol m (hmc.trans hm) hmn hnM tA s₀ htA hs₀' hwin hT G G' hcas hlev hinv hsucc hRn')
    (hl D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hgen
      hmol m (hml.trans hm) hmn hnM tA s₀ htA hs₀' hwin hT G G' hcas hlev hinv hsucc hRn')
    (hd D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hgen
      hmol m (hmd.trans hm) hmn hnM tA s₀ htA hs₀' hwin hT G G' hcas hlev hinv hsucc hRn')
    (he D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hgen
      hmol m (hme.trans hm) hmn hnM tA s₀ htA hs₀' hwin hT G G' hcas hlev hinv hsucc)

/-- **The profile proposition of one passage from its six ingredients.** -/
theorem passageProfileClauses_of_ingredients (hsm : SmoothRepOfHigherStatement)
    (hr0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageProfilesRegularStatement α s q ζ)
    (hc0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedCovarianceStatement α s q ζ)
    (hl0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedLiftStatement α s q ζ)
    (hd0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageDiscardedProfilesStatement α s q ζ)
    (he0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageErrorProfileStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ)
    (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    PassageProfileClausesStatement α s q ζ := by
  classical
  obtain ⟨Λr, hΛr, hr⟩ := hr0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λc, hΛc, hc⟩ := hc0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hl⟩ := hl0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λd, hΛd, hd⟩ := hd0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λe, hΛe, he⟩ := he0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max (max (max Λr Λc) (max Λl Λd)) Λe, by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cr, hcr, hr⟩ := hr Λ (by omega)
  obtain ⟨cc, hcc, hc⟩ := hc Λ (by omega)
  obtain ⟨cl, hcl, hl⟩ := hl Λ (by omega)
  obtain ⟨cd, hcd, hd⟩ := hd Λ (by omega)
  obtain ⟨ce, hce, he⟩ := he Λ (by omega)
  refine ⟨min (min (min cr cc) (min cl cd)) ce,
    lt_min (lt_min (lt_min hcr hcc) (lt_min hcl hcd)) hce, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK hPacc Q T₀ hQ hT₀ hPQ
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    hsched hNaux hNout L horders hwidths
  obtain ⟨SXr, SZr, Kr, hr⟩ := hr φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK
    hPacc Q T₀ hQ hT₀ hPQ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad σ₀ a σ hsched hNaux hNout L horders hwidths
  obtain ⟨SXc, SZc, Kc, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK
    hPacc Q T₀ hQ hT₀ hPQ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad σ₀ a σ hsched hNaux hNout L horders hwidths
  obtain ⟨SXl, SZl, Kl, hl⟩ := hl φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK
    hPacc Q T₀ hQ hT₀ hPQ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad σ₀ a σ hsched hNaux hNout L horders hwidths
  obtain ⟨SXd, SZd, Kd, hd⟩ := hd φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK
    hPacc Q T₀ hQ hT₀ hPQ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad σ₀ a σ hsched hNaux hNout L horders hwidths
  obtain ⟨SXe, SZe, Ke, he⟩ := he φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK
    hPacc Q T₀ hQ hT₀ hPQ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad σ₀ a σ hsched hNaux hNout L horders hwidths
  refine ⟨max (max (max SXr SXc) (max SXl SXd)) SXe,
    max (max (max SZr SZc) (max SZl SZd)) SZe,
    max (max (max Kr Kc) (max Kl Kd)) Ke, ?_⟩
  intro sX sZ hSX hSZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc hKs hKan hLan hJm
  obtain ⟨tr, CHr, Υr, hCHr, hΥr, hr⟩ := hr sX sZ ((((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hSX)
    ((((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hSZ) Ce kS hCe hc₀
    (hc₀upper.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))) hcr hcrupper hσf hlamC halloc
    ((((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hKs) ((((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hKan)
    ((((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hLan) ((((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hJm)
  obtain ⟨tc, CHc, Υc, hCHc, hΥc, hc⟩ := hc sX sZ ((((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hSX)
    ((((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hSZ) Ce kS hCe hc₀
    (hc₀upper.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))) hcr hcrupper hσf hlamC halloc
    ((((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hKs) ((((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hKan)
    ((((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hLan) ((((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hJm)
  obtain ⟨tl, CHl, Υl, hCHl, hΥl, hl⟩ := hl sX sZ ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hSX)
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hSZ) Ce kS hCe hc₀
    (hc₀upper.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hcr hcrupper hσf hlamC halloc
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hKs) ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hKan)
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hLan) ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hJm)
  obtain ⟨td, CHd, Υd, hCHd, hΥd, hd⟩ := hd sX sZ ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hSX)
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hSZ) Ce kS hCe hc₀
    (hc₀upper.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) hcr hcrupper hσf hlamC halloc
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hKs) ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hKan)
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hLan) ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hJm)
  obtain ⟨te, CHe, Υe, hCHe, hΥe, he⟩ := he sX sZ ((le_max_right _ _).trans hSX)
    ((le_max_right _ _).trans hSZ) Ce kS hCe hc₀
    (hc₀upper.trans (min_le_right _ _)) hcr hcrupper hσf hlamC halloc
    ((le_max_right _ _).trans hKs) ((le_max_right _ _).trans hKan)
    ((le_max_right _ _).trans hLan) ((le_max_right _ _).trans hJm)
  refine ⟨certificateThresholdJoin (certificateThresholdJoin (certificateThresholdJoin tr tc)
      (certificateThresholdJoin tl td)) te,
    max (max (max CHr CHc) (max CHl CHd)) CHe, max (max (max Υr Υc) (max Υl Υd)) Υe,
    hCHr.trans (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)), hΥr.trans_le (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)), ?_⟩
  intro kI hkI
  have hk1 := invariant_admissible_threshold_left hkI
  have hk2 := invariant_admissible_threshold_left hk1
  have hk3 := invariant_admissible_threshold_right hk1
  obtain ⟨CIr, Cwr, hr⟩ := hr kI (invariant_admissible_threshold_left hk2)
  obtain ⟨CIc, Cwc, hc⟩ := hc kI (invariant_admissible_threshold_right hk2)
  obtain ⟨CIl, Cwl, hl⟩ := hl kI (invariant_admissible_threshold_left hk3)
  obtain ⟨CId, Cwd, hd⟩ := hd kI (invariant_admissible_threshold_right hk3)
  obtain ⟨CIe, Cwe, he⟩ := he kI (invariant_admissible_threshold_right hkI)
  refine ⟨max (max (max CIr CIc) (max CIl CId)) CIe, max (max (max Cwr Cwc) (max Cwl Cwd)) Cwe, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  have hr := hr CI Cw j₀
    ⟨hledger.1, (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hledger.2.1,
      (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
    (IsCarrierStart.mono hA hT (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
      (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)) (zero_le_one.trans hCHr) hΥr.le hstart)
  have hc := hc CI Cw j₀
    ⟨hledger.1, (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hledger.2.1,
      (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
    (IsCarrierStart.mono hA hT (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
      (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)) (zero_le_one.trans hCHc) hΥc.le hstart)
  have hl := hl CI Cw j₀
    ⟨hledger.1, (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hledger.2.1,
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
    (IsCarrierStart.mono hA hT (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)) (zero_le_one.trans hCHl) hΥl.le hstart)
  have hd := hd CI Cw j₀
    ⟨hledger.1, (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hledger.2.1,
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
    (IsCarrierStart.mono hA hT (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)) (zero_le_one.trans hCHd) hΥd.le hstart)
  have he := he CI Cw j₀
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1,
      (le_max_right _ _).trans hledger.2.2.1, hledger.2.2.2⟩
    (IsCarrierStart.mono hA hT (le_max_right _ _)
      (le_max_right _ _) (zero_le_one.trans hCHe) hΥe.le hstart)
  intro Cn Cr Cj hCr hCj
  obtain ⟨mr, hr⟩ := hr
  obtain ⟨Cc, mc, hc⟩ := hc (1 + |Cn|)
  obtain ⟨Cl, ml, hl⟩ := hl (1 + |Cn|)
  obtain ⟨Cd, md, hd⟩ := hd (1 + |Cn|)
  obtain ⟨Ce', me, he⟩ := he
  have hC₁ : 0 ≤ |Cc| + |Cl| + |Cd| + |Ce'| := by positivity
  refine ⟨|Cn| + (|Cc| + |Cl| + |Cd| + |Ce'|) + (|Cc| + |Cl| + |Cd| + |Ce'|) * Cr +
      (|Cc| + |Cl| + |Cd| + |Ce'|) * Cj, max (max (max mr mc) (max ml md)) me, fun C hC => ?_⟩
  have hm1 := mul_nonneg hC₁ hCr
  have hm2 := mul_nonneg hC₁ hCj
  exact passageProfileClausesData_of_parts hq h128 hs₀ (by linarith)
    (Construction.Preservation.FullLift.successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq).le
    (by have := horders.1; omega) (by linarith) Cn Cr Cj (|Cc| + |Cl| + |Cd| + |Ce'|) C
    mr mc ml md me _ (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
    (le_max_right _ _) hC₁ hCr hCj
    (by linarith [le_abs_self Cn]) (by linarith [abs_nonneg Cn]) (by linarith [abs_nonneg Cn])
    hsm hr
    (hc _ (by linarith [le_abs_self Cc, abs_nonneg Cl, abs_nonneg Cd, abs_nonneg Ce']))
    (hl _ (by linarith [le_abs_self Cl, abs_nonneg Cc, abs_nonneg Cd, abs_nonneg Ce']))
    (hd _ (by linarith [le_abs_self Cd, abs_nonneg Cc, abs_nonneg Cl, abs_nonneg Ce']))
    (he _ (by linarith [le_abs_self Ce', abs_nonneg Cc, abs_nonneg Cl, abs_nonneg Cd]))

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **A classical representative from a higher Sobolev lift**.

`hilbert_classicalRep_exists` gives one classical representative per component; they assemble into
a function into the product, and the value jet of the truncation is a.e. the value jet of the lift.
Special cases: an empty family; `k = 0`, `n = 2`; `X = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.IterationPassage.Passage

/-- **A classical representative from a higher Sobolev lift** (`SmoothRepOfHigherStatement`). -/
theorem smoothRepOfHigher : SmoothRepOfHigherStatement := by
  intro S k n hkn X Xn hXn
  choose a ha using fun v : CompIn S => hilbert_classicalRep_exists n k hkn (Xn v)
  refine ⟨fun x v => a v x, ?_, ?_, ?_⟩
  · exact contDiff_pi.mpr fun v => (ha v).2.1
  · intro j x
    funext v
    exact (ha v).2.2.1 j x
  · intro v
    have h1 := IterationPassage.torus_truncate_value_ae (Nat.zero_le n) (Xn v)
    rw [hXn v] at h1
    exact h1.trans (classicalRep_value_ae (Xn v) (a v) (ha v))

end AVRegularity.IterationPassage.Passage
end
end
end
