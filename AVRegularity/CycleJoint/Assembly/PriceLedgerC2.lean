-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.Assembly.PatchModelBound
public import AVRegularity.CycleJoint.Assembly.PriceLedgerSeam
public import AVRegularity.CycleJoint.Assembly.BlockTransportedRemainderTime
import AVRegularity.CycleWords.Assembly.SeamNorms

section
/-! **The parts of the patch error**.

With the cover centred at the transported patch centre:
- `twoReturn_weighted_le`: the weighted pullback bound for the return of the two-block theorem at the slots `K` (radius `ρ ≤ E`, any moment);
- `physical_tp_eq_return`: the physical solution at `t_p` is the return of its following-chart
  curve at the cell time of `t_p`;
- `model_moment_le`: a truncation of the returned model at radius `r ≤ R` has at most the weighted
  energy of the model bound;
- `seam_error_return_le`: the return of the seam's masked error, unweighted, is at most
  `C_comp² (CN · price)²` times the `L²` norm of the localized datum.

For an empty index type the sums are `0`; when all slots are `0` only values enter. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Parts

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The constant of the return of the two-block theorem at moment `n` (uniform over the slots `K ≤ Kmax`). -/
def returnConstant (Cchart : ℕ → ℝ) (E : ℝ) (Kmax n : ℕ) : ℝ :=
  (2 * preparationPieceFlowJetBudget Cchart E 1) ^ (2 * n) *
    compositionFactorialNormBound (preparationFlowJetConstant Cchart) Kmax ^ 2

theorem returnConstant_nonneg (Cchart : ℕ → ℝ) (E : ℝ) (Kmax n : ℕ) :
    0 ≤ returnConstant Cchart E Kmax n := by
  unfold returnConstant
  rw [preparationPieceFlowJetBudget_one]
  have := le_max_right (Cchart 0) 0
  positivity

/-- **The weighted pullback bound for the return of the two-block theorem** at the slots `K`. -/
theorem twoReturn_weighted_le (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (i : ι)
    (V : PlaneHk Set.univ (K i) (h i)) :
    weightedFactorialNormSq n (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) ρ (K i)
        (twoReturn hp hΛ hchart i V) ≤
      ENNReal.ofReal (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax n) *
        (ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
          weightedFactorialNormSq n (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
            (ρ / ocEpsilon q Λ m) (K i) V) := by
  have hεpos : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hE : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ
  obtain ⟨hL1, hlip⟩ := preparationWindowReference_inverse_flow_lipschitz hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1))
    (twoTp α q Λ m l₀) (hp.windows hΛ).tpMem
  have h := preparationWindowReferenceCellReturn_weighted_le hW hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1)) (K i)
    (slot_le_chart hp.hK hchart i) hE (ocEpsilon q Λ m) hεpos.ne' (twoYcPost hp)
    (twoTp α q Λ m l₀) (hp.windows hΛ).tpMem hρ hρE _ hL1 hlip n
    (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
    (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) V
  rw [return_centre_eq hp N j hyc, sub_self, smul_zero] at h
  have e1 : (Real.sqrt (B * ocTauPP α q Λ m))⁻¹ * ocEpsilon q Λ m =
      ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) := by ring
  have e3 : |((ocEpsilon q Λ m)⁻¹ ^ 2)⁻¹| = ocEpsilon q Λ m ^ 2 := by
    rw [inv_pow, inv_inv, abs_of_nonneg (sq_nonneg _)]
  rw [e1, e3] at h
  refine h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  unfold returnConstant
  have hB : 0 ≤ 2 * preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) 1 := by
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (compositionFactorialNormBound_nonneg _ _)
    (compositionFactorialNormBound_mono _ (hp.hK i)) 2) (pow_nonneg hB _)

/-- The physical solution at `t_p` is the return of its following-chart curve. -/
theorem physical_tp_eq_return (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) {Y : Type*} (U : Y → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (ξ : Y) (i : ι) :
    U ξ i (twoTp α q Λ m l₀) =
      twoReturn hp hΛ hchart i (twoUHpost hp hΛ hchart U ξ i (cellTime q Λ m ν (twoTp α q Λ m l₀))) :=
  (preparationWindowReferenceCellNativeCurve_return hp.hprep hp.hcover _ (hp.windows hΛ).next
    (ocA_nonneg_of hΛ (m - 1)) (K i) (slot_le_chart hp.hK hchart i) ν hp.cov.pos.1.ne'
    (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYcPost hp) (U ξ i)
    (twoTp α q Λ m l₀) (hp.windows hΛ).tpMem).symm

end Parts

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A truncation at radius `r ≤ R` has at most the weighted energy of the untruncated field of
order `Mb` at radius `R`. -/
theorem model_moment_le (π : ι → ℝ) (K : ι → ℕ) {Mb : ℕ} (hKM : ∀ i, K i ≤ Mb) (n : ℕ)
    (ϖ : ℝ) (y : Vec 2) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (X : ∀ i, PlaneHk Set.univ Mb (h i)) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ y r (K i) (truncatePlaneHk (hKM i) (X i)) ≤
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y R Mb (X i) := by
  refine Finset.sum_le_sum fun i _ => mul_le_mul_right ?_ _
  rw [CycleWords.weightedFactorialNormSq_truncate (hKM i) le_rfl]
  exact (weightedFactorialNormSq_order_mono n ϖ y r (hKM i) (X i)).trans
    (Weighted.weightedFactorialNormSq_radius_mono n ϖ y hr hrR Mb (X i))

/-- The price identity `c ε² (C M)² = c C² S` when `M² = ε⁻² S`. -/
theorem ennreal_scaled_price_eq {c C e S : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (he : e ≠ 0)
    {M : ℝ≥0∞} (hM : M ^ 2 = ENNReal.ofReal ((e ^ 2)⁻¹ * S)) :
    ENNReal.ofReal c * ENNReal.ofReal (e ^ 2) * (ENNReal.ofReal C * M) ^ 2 =
      ENNReal.ofReal (c * C ^ 2 * S) := by
  rw [mul_pow, hM, ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_mul (sq_nonneg C), ← ENNReal.ofReal_mul (mul_nonneg hc (sq_nonneg e))]
  congr 1
  field_simp

/-- The seam's masked error controls the cell error of the truncated model, unweighted. -/
theorem seam_error_cell_le (π : ι → ℝ) (K : ι → ℕ) {Kmax Mb : ℕ} (hK : ∀ i, K i ≤ Kmax)
    (hKM : ∀ i, K i ≤ Mb) (pout : ℕ) (ϖ r' : ℝ) (hr' : 0 ≤ r')
    (uFsum : ∀ i, PlaneHk Set.univ (K i) (h i)) (V : ∀ i, PlaneHk Set.univ Mb (h i))
    (G : ∀ x, Vec 2 → h x)
    (hV : ∀ v a, a ≤ Mb → ∀ w, planeJetOrder (V v) a w =ᵐ[volume] orderedDerivative w (G v))
    (hG : ∀ v (k : ℕ), ContDiff ℝ k (G v)) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq 0 ϖ 0 r' (K i) (uFsum i - truncatePlaneHk (hKM i) (V i)) ≤
      weightedJetNorm π (pout : ℝ) Kmax ϖ r'
        (fun x a' wd z => if a' ≤ K x then
          planeJetOrder (uFsum x) a' wd z - orderedDerivative wd (G x) z else 0) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_right
    ((weightedFactorialNormSq_moment_mono (Nat.zero_le pout) _ _ _ _ _).trans
      (weightedFactorialNormSq_order_mono pout ϖ 0 r' (hK i) _)) _) ?_
  refine weightedFactorialNormSq_family_le_weightedJetNorm_sq π pout Kmax ϖ r' hr'
    (fun i => uFsum i - truncatePlaneHk (hKM i) (V i)) _ (fun v a _ w => ?_) (fun v a w => ?_)
  · by_cases ha : a ≤ K v
    · have h1 := CycleWords.planeJetOrder_sub_ae ha (uFsum v) (truncatePlaneHk (hKM v) (V v)) w
      rw [CycleWords.planeJetOrder_truncate (hKM v) ha] at h1
      filter_upwards [h1, hV v a (ha.trans (hKM v)) w] with z hz1 hz2
      simp only [hz1, hz2, ha, ↓reduceIte]
    · refine Filter.Eventually.of_forall fun z => ?_
      simp only [planeJetOrder, ha, ↓reduceDIte, ↓reduceIte]
  · by_cases ha : a ≤ K v
    · simp only [ha, ↓reduceIte]
      exact (CycleWords.Assembly.planeJetOrder_aestronglyMeasurable (uFsum v) a w).sub
        (CycleWords.Assembly.orderedDerivative_continuous w (hG v a)).aestronglyMeasurable
    · simp only [ha, ↓reduceIte]
      exact aestronglyMeasurable_const

end Generic

section Seam

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- **The return of the seam's masked error**, unweighted: at most
`returnConstant₀ (CN · price)²` times the `L²` norm of the localized datum. -/
theorem seam_error_return_le (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    {Mb : ℕ} (hKM : ∀ i, K i ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (pout : ℕ) (CNp : ℝ) (hCNp : 0 ≤ CNp) (ξ : ∀ i, TorusHk (K i) (h i))
    (uFsum : ∀ i, PlaneHk Set.univ (K i) (h i))
    (herr : weightedJetNorm π (pout : ℝ) Kmax (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (r / ocEpsilon q Λ m)
        (fun x a' wd z => if a' ≤ K x then
          planeJetOrder (uFsum x) a' wd z - orderedDerivative wd (Mc ξ x) z else 0) ≤
      ENNReal.ofReal CNp * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x))) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq 0
        (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) r (K i)
        (twoReturn hp hΛ hchart i
          (uFsum i - truncatePlaneHk (hKM i) (realizeCellModel Mb Mc hsm hmem ξ i))) ≤
      ENNReal.ofReal (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0 * CNp ^ 2 *
        ∑ i, (π i)⁻¹ *
          ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le (K i)) (ξ i))‖ ^ 2) := by
  have hεpos : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hr0 : 0 ≤ r := hp.cov.pos.2.2.le
  have hc := returnConstant_nonneg Cchart (ocEpsilon q Λ (m - 1)) Kmax 0
  have hcell := seam_error_cell_le π K hp.hK hKM pout
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m)
    (div_nonneg hr0 hεpos.le) uFsum (realizeCellModel Mb Mc hsm hmem ξ) (Mc ξ)
    (fun v a ha w => realizeCellModel_jet_ae Mb Mc hsm hmem ξ v a ha w) (hsm ξ)
  have hmom := twoV₀_momentNorm_sq hΛ hchart hζ hp N hN j ξ
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
  calc _ ≤ ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        (ENNReal.ofReal (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0) *
          (ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
            weightedFactorialNormSq 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
              (r / ocEpsilon q Λ m) (K i)
              (uFsum i - truncatePlaneHk (hKM i) (realizeCellModel Mb Mc hsm hmem ξ i)))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_right
          (twoReturn_weighted_le hW hΛ hchart hp N j hyc 0 hr0 (hp.cov.rho_e.trans heE) i _) _
    _ = ENNReal.ofReal (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0) *
          ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
              (r / ocEpsilon q Λ m) (K i)
              (uFsum i - truncatePlaneHk (hKM i) (realizeCellModel Mb Mc hsm hmem ξ i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ ENNReal.ofReal (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0) *
          ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
          (ENNReal.ofReal CNp * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
            (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x))) ^ 2 :=
        mul_le_mul_right (hcell.trans (pow_le_pow_left₀ zero_le herr 2)) _
    _ = _ := ennreal_scaled_price_eq hc hCNp hεpos.ne' hmom

end Seam

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The two-block theorem on its window, from the block word geometry**.

`twoBlockJoint_of_blockWordGeometry`: `BlockWordGeometryStatement` gives the two-block theorem
(`TwoBlockJointStatement`). The weights `Cw` and the threshold `Λ₀` are those of the weights
theorem with no gain (`twoBlockWeights_exists`); the constants are those of the block word geometry, the first-block energy
constant, the following-block energy constant, and the gain constant `max (max CTa CTb) CT` of
the two summaries and the block word geometry. The body (`twoBlockJoint_body`) runs the three stages: the old block
(`twoBlockJoint_old`), the future block over the old word endpoints (`twoBlockJoint_future`), and
the energy with the finish (`twoBlockJoint_energy`). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- **The chart weights of a subwindow** at moment order `N` (the weights theorem with its
metric written as `windowCoverCellMetric`). -/
def TwoBlockWeights (α q : ℝ) (ζ : ℝ → ℝ) (Cw : ℕ → ℝ) (Λ₀ N : ℕ) : Prop :=
  ∀ Λ : ℕ, Λ₀ ≤ Λ →
  ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ) (M : ℕ) (κ : ℕ → ℝ),
    IsOCBandChain α q Λ ζ M κ →
  ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ (ν B : ℝ), κ m = ν → κ (m - 1) = B →
  ∀ (hφ : IsAdmissibleStream (Φ (m - 1)))
    (tA tZ ρs g g0 a B₀ lam Cb : ℝ) (qJ Kmax : ℕ) (CG : ℕ → ℝ)
    (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2),
    IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀ →
    g ≤ 1 → g0 ≤ 1 / 4 →
  ∀ (i : Fin (P + 2)) (u0 u1 : ℝ), u0 < u1 →
    Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i →
    u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    Nonempty (ChartWeights (windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ i)
      (ocCellDrift α q Λ ζ m ν (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i))
      u0 (u1 - u0) (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 N Cw) ∧
    Nonempty (ChartWeights
      (fun t _ => windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ i t 0)
      (ocCellDrift α q Λ ζ m ν (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i))
      u0 (u1 - u0) (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 N Cw)

/-- **The universal weights** (the weights theorem with no gain). -/
theorem twoBlockWeights_exists {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Cw : ℕ → ℝ, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ N : ℕ, ∃ L : ℕ, 1 ≤ L ∧
      (∀ k ≤ N, Real.exp (18 * Cw k) / (L : ℝ) ^ 2 ≤ 1 / 16) ∧
        TwoBlockWeights α q ζ Cw Λ₀ N := by
  obtain ⟨Cw, Λ₀, h128, hw⟩ := windowCover_uniform_subwindow_weights_with_gains hα0 hα1 hs0 hs1
    hq hζ (Fin.elim0 : Fin 0 → ℝ)
  refine ⟨Cw, Λ₀, h128, fun N => ?_⟩
  obtain ⟨L, hL, hres, hW⟩ := hw N
  refine ⟨L, hL, hres, ?_⟩
  intro Λ hΛ Φ M κ hκ m hm2 hmM ν B hν hB hφ tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀ cov hg
    hg0 i u0 u1 hu hwin hlen
  have hWi := hW Λ hΛ Φ M κ hκ m hm2 hmM ν B hν hB hφ tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀
    cov hg hg0 i u0 u1 hu hwin hlen
  exact ⟨hWi.1, hWi.2.1⟩

/-- A gain bound for a larger constant gives it for a smaller one. -/
theorem gain_mono {a b g ζ : ℝ} (hab : a ≤ b) (hg : 0 ≤ g) (hζ : 0 ≤ ζ)
    (h : ENNReal.ofReal (b * g * ζ) ≤ 1) : ENNReal.ofReal (a * g * ζ) ≤ 1 :=
  (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hg) hζ)).trans h

/-- **The body of the two-block theorem** from the three stages and the weights of the two windows. -/
theorem twoBlockJoint_body (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (Cm Cchart CG : ℕ → ℝ) (Cprep CT CR Cterminal Crem : ℝ) {α s q : ℝ}
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Cw : ℕ → ℝ) (Λ₀ : ℕ)
    (h128 : 128 ≤ Λ₀) (Cenergy1 CTa CTb Cenergy2 : ℝ)
    (hO : TwoBlockOldBody.{u, v, w, x} D Ks Kmax Jchart Jm hchart Cm Cchart CG Cprep CT CR
      Cterminal Crem Cenergy1 CTa)
    (hF : TwoBlockFutureBody.{u, v, w, x} D Ks Kmax Jchart Jm hchart Cm Cchart CG Cprep CT CR
      Cterminal Crem α q ζ CTb)
    (hE : ∀ (Cw : ℕ → ℝ) (Cenergy1 : ℝ) (Npre Npost Lpre Lpost : ℕ),
      TwoBlockEnergyBody.{u, v, w, x} D Ks Kmax Jchart Jm hchart Cm Cchart CG Cprep CR Cterminal
        Crem α q hζ Cw Cenergy1 Cenergy2 Npre Npost Lpre Lpost)
    (Npre Npost Lpre Lpost : ℕ) (hLpre : 1 ≤ Lpre) (hLpost : 1 ≤ Lpost)
    (hrPre : ∀ k ≤ Npre, Real.exp (18 * Cw k) / (Lpre : ℝ) ^ 2 ≤ 1 / 16)
    (hrPost : ∀ k ≤ Npost, Real.exp (18 * Cw k) / (Lpost : ℝ) ^ 2 ≤ 1 / 16)
    (hWpre : TwoBlockWeights α q ζ Cw Λ₀ Npre) (hWpost : TwoBlockWeights α q ζ Cw Λ₀ Npost) :
    TwoBlockJointBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG Cenergy1
      Cenergy2 Cprep (max (max CTa CTb) CT) CR Cterminal Crem Npre Npost Lpre Lpost := by
  intro Λ hΛ₀ hΛ g₀ hg₀ H Ls qJ hD hKs hqJ Ca Cth Cb COld Crat Cpad Cage Npad mStar ι _ _ h _ _ _
    _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A Θ T r ρold hp S hcoreS hquiet
    Npatch hNpatch patch Jpre Jpost hNpre hNpost hgain θM₁ θS₁ θM₂ θS₂ bM₁ bS₁ bM₂ bS₂
  have hΛ128 : 128 ≤ Λ := h128.trans hΛ₀
  have hwin := hp.windows hΛ
  obtain ⟨-, -, hgsmall, hg0, -⟩ := hp.scales hq hΛ128 hg₀
  have hg1 : g ≤ 1 := by linarith only [hgsmall]
  have hζc : 0 ≤ Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) :=
    div_nonneg (Real.sqrt_nonneg _) (Construction.Stream.ocEpsilon_pos hΛ).le
  have hgainO := gain_mono (max_le_max (le_max_left CTa CTb) le_rfl) hp.cov.g_range.1 hζc hgain
  have hgainF := gain_mono (max_le_max (le_max_right CTa CTb) le_rfl) hp.cov.g_range.1 hζc hgain
  have hNle : Npost ≤ Npre :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hNpre)
  have hWo := hWpre Λ hΛ₀ Φ M' κ hp.hband m hp.hm2 hp.hmM ν B hp.hν hp.hB hφ tS
    (tS + 2 * ocTauPP α q Λ m) r g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀ hp.cov hg1 hg0
    (windowCoverReferenceChartIndex P) _ _ hwin.ab hwin.windowPre hwin.lengthPre
  have hWf := hWpost Λ hΛ₀ Φ M' κ hp.hband m hp.hm2 hp.hmM ν B hp.hν hp.hB hφ tS
    (tS + 2 * ocTauPP α q Λ m) r g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀ hp.cov hg1 hg0
    (windowCoverFollowingChartIndex P hp.cov.P_pos) _ _ hwin.bd hwin.windowPost hwin.lengthPost
  obtain ⟨uphys, wphys, Upre, Bdpre, hpre, Tpre', Tpre, hOf⟩ := hO hq Λ hΛ128 hΛ hζ g₀ hg₀ H Ls qJ
    hD hKs hqJ Ca Cth Cb COld Crat Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀
    F actual A Θ T r ρold hp S hcoreS hquiet Npatch hNpatch patch Jpre Npre Npost hNpre Cw
    hWo.1.some hWo.2.some Lpre hLpre hrPre hgainO θM₁ θS₁ bM₁ bS₁
  obtain ⟨V₀', uphys', wphys', Bdpost, hpost, Tret, hFf⟩ := hF Λ hΛ128 hΛ g₀ hg₀ H Ls qJ hD hKs
    hqJ Ca Cth Cb COld Crat Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
    A Θ T r ρold hp S hcoreS hquiet Jpre Jpost Npost hNpost Cw hWf.1.some hWf.2.some Lpost hLpost
    hrPost hgainF θM₂ θS₂ bM₂ bS₂ Tpre' Tpre hOf.2.2.2.2.2.2.1 hOf.2.2.2.2.2.1
  exact hE Cw Cenergy1 Npre Npost Lpre Lpost Λ hΛ128 hΛ g₀ hg₀ H Ls qJ hD hqJ Ca Cth Cb COld Crat
    Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T r ρold hp Npatch
    hNpatch patch Jpre Jpost hNle θM₁ θS₁ θM₂ θS₂ bM₁ bS₁ bM₂ bS₂ hWf.1.some uphys wphys Upre Bdpre
    hpre Tpre' Tpre hOf V₀' uphys' wphys' Bdpost hpost Tret hFf

/-- **The two-block theorem, from the block word geometry.** -/
theorem twoBlockJoint_of_blockWordGeometry
    (hC1 : BlockWordGeometryStatement.{u, v, w, x, max u v}) :
    TwoBlockJointStatement.{u, v, w, x} := by
  intro α s q hα0 hα1 hs0 hs1 hq ζ hζ
  obtain ⟨Cw, Λ₀, h128, hw⟩ := twoBlockWeights_exists hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Cw, Λ₀, h128, ?_⟩
  intro D Ks Kmax Jchart Jm hchart hmol hKsJ Cm Cchart CG
  obtain ⟨Cprep, CT, CR, Cterminal, Crem, hCprep, hCT, hCR, hCterminal, hCrem, hC⟩ :=
    hC1 D Ks Kmax Jchart Jm hchart hmol hKsJ Cm Cchart CG
  obtain ⟨Cenergy1, CTa, he1, -, hO⟩ :=
    twoBlockJoint_old D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG Cprep CT CR Cterminal Crem hC
  obtain ⟨CTb, -, hF⟩ := twoBlockJoint_future D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG Cprep
    CT CR Cterminal Crem hC hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cenergy2, hCe2, hE⟩ := twoBlockJoint_energy D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG
    Cprep CR Cterminal Crem hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Cenergy1, Cenergy2, Cprep, max (max CTa CTb) CT, CR, Cterminal, Crem, he1, hCe2, hCprep,
    le_max_of_le_right hCT, hCR, hCterminal, hCrem, fun Npre Npost => ?_⟩
  obtain ⟨Lpre, hLpre, hrPre, hWpre⟩ := hw Npre
  obtain ⟨Lpost, hLpost, hrPost, hWpost⟩ := hw Npost
  exact ⟨Lpre, Lpost, hLpre, hLpost, twoBlockJoint_body D Ks Kmax Jchart Jm hchart Cm Cchart CG
    Cprep CT CR Cterminal Crem hq hζ Cw Λ₀ h128 Cenergy1 CTa CTb Cenergy2 hO hF hE Npre Npost Lpre
    Lpost hLpre hLpost hrPre hrPost hWpre hWpost⟩

/-- **The two-block theorem** (unconditional: the block word geometry from the block edge package and the letter
fluxes). -/
theorem twoBlockJoint : TwoBlockJointStatement.{u, v, w, x} :=
  twoBlockJoint_of_blockWordGeometry
    (blockWordGeometry_of_package blockEdgePackage metricLetterFlux sourceLetterFlux)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The moments of the physical solution at `t_p`, in the following chart**.

The error of the one-patch statement must have every fixed output moment bounded without the small factor.
For the physical part this is the energy of the actual solution:
the old block's first-block energy (the first summary, through `twoBlockJoint_old`: the
reference-chart curve at the seam has moment-`Npre` energy at most `twoCfirst · twoEin Npre`) and
the following block's homogeneous endpoint energy (`following_actual_endpoint_energy`, with the
chart weights of the future window at moment `n ≤ Npre`) bound the following-chart curve of the
physical solution at every cell time of the future block, in particular at the cell time of `t_p`.

The physical solution is the old block's (`twoPhysical`); the one-patch statement identifies it with its own plane
solution at `t_p` by uniqueness.

For an empty index type both sides are `0`. For `n = 0` the energy is unweighted, for `H = 0` the
rank factors are `1`, and for `Θ = 0` there is no source coupling (`θ = 0`). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The price of the moments of the physical solution at the end of the future block. -/
def twoMomentPrice (Cw : ℕ → ℝ) (Kmax D H : ℕ) (CG : ℕ → ℝ) (Cprep θ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax (fun j => max (CG j) 0) Cw D
      (Cprep * θ)) ^ (2 * H)) *
    (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax (fun j => max (CG j) 0) Cw)) *
    ENNReal.ofReal (cellTransitionMomentBudget Kmax n)

/-- **The body of the moment statement**: for every family with the joint premises, every patch, a moment order
`n ≤ Npre` and the gain, the old block's physical solution has, in the following chart at the cell
time of `t_p`, moment-`n` energy at most the moment price times `twoCfirst · twoEin Npre`. -/
def TwoBlockMomentBody (α q : ℝ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Cw : ℕ → ℝ) (Λ₀ : ℕ)
    (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (Cm Cchart CG : ℕ → ℝ)
    (Cenergy1 Cprep CTm : ℝ) (n Npre : ℕ) : Prop :=
  ∀ (Λ : ℕ) (_hΛ₀ : Λ₀ ≤ Λ) (hΛ : 1 ≤ Λ) (g₀ : ℝ) (_hg₀ : g₀ ≤ 1 / 32) (H Ls qJ : ℕ)
    (_hD : 2 ≤ D) (_hKs : Ks + 1 ≤ Jm) (_hqJ : Ks + 1 + Kmax ≤ qJ)
    (Ca Cth Cb COld Crat Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (S : Set ℝ) (_hcoreS : IsCoreOutside α q Λ m F tS (tS + 2 * ocTauPP α q Λ m) S)
    (_hquiet : F.IsFastIndependentOn (S ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (_hNpre : (Ks + 1) + H * (Ks + 1) ≤ Npre)
    (_hgain : ENNReal.ofReal (CTm * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1),
    ∃ (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      twoPhysical hp hζ Npatch hNpatch patch uphys wphys ∧
      ∀ ξ, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
            (r / ocEpsilon q Λ m) (K i)
            (twoUHpost hp hΛ hchart uphys ξ i (cellTime q Λ m ν (twoTp α q Λ m l₀))) ≤
        twoMomentPrice.{u, v} Cw Kmax D H CG Cprep (max Cth 0 * Θ) n *
          (twoCfirst hp Cw Cenergy1 Npre * twoEin hp hΛ hchart hζ Npatch hNpatch patch Npre ξ)

/-- **The moment body from the old block and the following-block energy.** -/
theorem twoBlockMoment_body (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (Cm Cchart CG : ℕ → ℝ) (CprepC CT CR Cterminal Crem : ℝ)
    {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Cw : ℕ → ℝ) (Λ₀ : ℕ)
    (h128 : 128 ≤ Λ₀) (Cenergy1 CTa Cprep : ℝ)
    (hO : TwoBlockOldBody.{u, v, w, x} D Ks Kmax Jchart Jm hchart Cm Cchart CG CprepC CT CR
      Cterminal Crem Cenergy1 CTa)
    (hfol : ∀ (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
      (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hB : ∀ i j, 0 ≤ B i j),
    ∀ (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
      (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output),
      F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
      IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
        ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    ∀ (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Set.Icc tS tZ)
      (a b θ : ℝ),
      Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
      (∀ i, ∑ j, B i j ≤ θ) → (∀ j, ∑ i, B i j ≤ θ) →
    ∀ H : ℕ, F.HasDepthAtMost H → F.IsDescending K →
    ∀ (ζ : ℝ → ℝ) (Bcover g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ)
      (CG : ℕ → ℝ) (y₀ : Vec 2)
      (cov : IsWindowCover α q Λ m ζ Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
      (hΛ : 128 ≤ Λ), IsFastProfile ζ → a ≤ b →
    let ic := windowCoverFollowingChartIndex P cov.P_pos
    Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
      max Kmax 1 ≤ qJ → g ≤ 1 / 4 → 2 ≤ D →
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    let r := ρ / ocEpsilon q Λ m
    let σ := ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m
    let _A := preparationReferenceCellSourceCoefficient F hφ σ
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    e = ocEpsilon q Λ m →
    IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)) →
    ∀ Nperiod : ℕ, (ocEpsilon q Λ m)⁻¹ = (Nperiod : ℝ) →
    ∀ (s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      IsAdmissibleQ α s q → IsOCStreamSeq α q Λ ζ Φ → 1 ≤ m →
    ∀ (ha : 0 ≤ ocA α q Λ (m - 1)) (tp : ℝ) (htp : tp ∈ Set.Icc tS tZ),
    a = (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tp) →
    (∀ t ∈ Set.Icc a b,
      (((l₀ + 1 : ℤ) : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ (((l₀ + 1 : ℤ) : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
    let hΛ1 : 1 ≤ Λ := (by omega)
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc0 := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let _S := preparationReferenceCellTransitionFamilyLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ1).le ha K (fun i => by have hh := _hK i; omega)
      σ hnext (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 yc tp htp
    ∀ (n : ℕ) (Cw : ℕ → ℝ) (ϖ : ℝ) (_W : ChartWeights G v a (b - a) ϖ 0 n Cw),
    ∀ {X : Type (max u v)} [AddCommGroup X] [Module ℝ X]
      (Upre : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hUinit : ∀ ξ i, weightedFactorialNormSq n ϖ 0 r (K i) (Upre ξ i) ≠ ⊤)
      (Uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Uwphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ ξ, ∃ f : ∀ i, PlaneHk Set.univ (K i) (h i),
      IsCoupledWeakSolutionPlane ν tS tZ (streamVel (Φ m)) D K
        (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K)
        f (fun _ _ => 0) (fun _ _ => 0) (Uphys ξ) (Uwphys ξ)) →
    (∀ ξ i, Upre ξ i = preparationReferenceCellNativeCurve hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ1).le ha (K i) (by have hh := _hK i; omega)
      ν (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 (Uphys ξ i) a) →
    let Cjet := fun j => max (CG j) 0
    let Cactual := ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
      (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw))
    ∀ ξ, ∀ t ∈ Set.Icc a b,
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i)
        (preparationWindowReferenceCellNativeCurve hprep hcover σ hnext ha
          (K i) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
          (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc (Uphys ξ i) t)) ≤
        Cactual * (ENNReal.ofReal (cellTransitionMomentBudget Kmax n) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (Upre ξ i)))
    (n Npre : ℕ) (hn : n ≤ Npre) (Lpre : ℕ) (hLpre : 1 ≤ Lpre)
    (hrPre : ∀ k ≤ Npre, Real.exp (18 * Cw k) / (Lpre : ℝ) ^ 2 ≤ 1 / 16)
    (hWpre : TwoBlockWeights α q ζ Cw Λ₀ Npre) (hWn : TwoBlockWeights α q ζ Cw Λ₀ n) :
    TwoBlockMomentBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG Cenergy1
      Cprep (max CTa CT) n Npre := by
  intro Λ hΛ₀ hΛ g₀ hg₀ H Ls qJ hD hKs hqJ Ca Cth Cb COld Crat Cpad Cage Npad mStar ι _ _ h _ _ _
    _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A Θ T r ρold hp S hcoreS hquiet
    Npatch hNpatch patch hNpre hgain
  have hΛ128 : 128 ≤ Λ := h128.trans hΛ₀
  have hwin := hp.windows hΛ
  obtain ⟨heE, hper, hgsmall, hg0, hm⟩ := hp.scales hq hΛ128 hg₀
  obtain ⟨hBnn, hrow, hcol, -⟩ := hp.sums
  have hg1 : g ≤ 1 := by linarith only [hgsmall]
  have hWo := hWpre Λ hΛ₀ Φ M' κ hp.hband m hp.hm2 hp.hmM ν B hp.hν hp.hB hφ tS
    (tS + 2 * ocTauPP α q Λ m) r g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀ hp.cov hg1 hg0
    (windowCoverReferenceChartIndex P) _ _ hwin.ab hwin.windowPre hwin.lengthPre
  have hWf := hWn Λ hΛ₀ Φ M' κ hp.hband m hp.hm2 hp.hmM ν B hp.hν hp.hB hφ tS
    (tS + 2 * ocTauPP α q Λ m) r g g₀ a B₀ lam Cb qJ Kmax CG l₀ P y₀ hp.cov hg1 hg0
    (windowCoverFollowingChartIndex P hp.cov.P_pos) _ _ hwin.bd hwin.windowPost hwin.lengthPost
  have hNpre' : 0 + (Ks + 1) + (0 + H) * (Ks + 1) ≤ Npre := by simpa only [zero_add] using hNpre
  obtain ⟨uphys, wphys, Upre, Bdpre, hpre, Tpre', Tpre, hOf⟩ := hO hq Λ hΛ128 hΛ hζ g₀ hg₀ H Ls qJ
    hD hKs hqJ Ca Cth Cb COld Crat Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀
    F actual A Θ T r ρold hp S hcoreS hquiet Npatch hNpatch patch 0 Npre 0 hNpre' Cw
    hWo.1.some hWo.2.some Lpre hLpre hrPre hgain 0 0 (fun _ _ => 0) (fun _ _ => 0)
  have hsc := windowCover_native_subwindow_scales hΛ hφ hp.cov
    (windowCoverFollowingChartIndex P hp.cov.P_pos) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀)) hwin.windowPost
  have hG4 := hfol α q Λ m Φ hφ tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad l₀ P ν
    (ocEpsilon q Λ m) r hp.cov.pos.1 hp.cov.pos.2.2 hp.cov.rho_e heE F π hp.hπ K hp.hK actual
    (fun v u => Real.sqrt (π u / π v) * A v u) hBnn hp.hprep hp.hcover hp.hmeas hp.hwmeas
    hp.hpointwise hwin.next (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀)) (max Cth 0 * Θ) hsc.1 hrow hcol H hp.hdepth hp.hdesc ζ B
    g g₀ a B₀ lam Cb qJ CG y₀ hp.cov hΛ128 hζ hwin.bd.le hwin.windowPost
    (max_one_le_of_reserve hqJ) (by linarith only [hgsmall]) hD rfl hp.htorus
    (Classical.choose hper) (Classical.choose_spec hper) s hα0 hα1 hs0 hs1 hq hp.hΦ hm
    (ocA_nonneg_of hΛ (m - 1)) (ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)))
    hwin.seamMem hwin.seamTime.symm hwin.blockPost n Cw
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) hWf.1.some Upre
    (fun ξ i => hOf.2.2.2.1 ξ n hn i) uphys wphys
    (hp.physical_exists hζ Npatch hNpatch patch uphys wphys hOf.1) hOf.2.1
  refine ⟨uphys, wphys, hOf.1, fun ξ => ?_⟩
  have h1 := hG4 ξ (cellTime q Λ m ν (twoTp α q Λ m l₀)) ⟨hwin.bd.le, le_rfl⟩
  have hmono : ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
        (r / ocEpsilon q Λ m) (K i) (Upre ξ i) ≤
      twoCfirst hp Cw Cenergy1 Npre * twoEin hp hΛ hchart hζ Npatch hNpatch patch Npre ξ :=
    (Finset.sum_le_sum fun i _ => mul_le_mul_right
      (weightedFactorialNormSq_moment_mono hn _ _ _ _ _) _).trans (hOf.2.2.1 ξ)
  refine (h1.trans (mul_le_mul_right (mul_le_mul_right hmono _) _)).trans (le_of_eq ?_)
  unfold twoMomentPrice
  ring

/-- **The moments of the physical solution**: the weights and threshold are universal; after the orders and the supplied bounds, the
first-block constant `Cenergy1`, the preparation constant `Cprep` and the gain constant `CTm`;
then the moment order `n ≤ Npre`. -/
theorem twoBlockMoment {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ (Cw : ℕ → ℝ) (Λ₀ : ℕ), 128 ≤ Λ₀ ∧
    ∀ (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
      (_hKsJ : Ks + D + 2 ≤ Jchart) (Cm Cchart CG : ℕ → ℝ),
    ∃ Cenergy1 Cprep CTm : ℝ, 1 ≤ Cenergy1 ∧ 1 ≤ Cprep ∧ 0 ≤ CTm ∧
    ∀ n Npre : ℕ, n ≤ Npre →
      TwoBlockMomentBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG
        Cenergy1 Cprep CTm n Npre := by
  obtain ⟨Cw, Λ₀, h128, hw⟩ := twoBlockWeights_exists hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Cw, Λ₀, h128, ?_⟩
  intro D Ks Kmax Jchart Jm hchart hmol hKsJ Cm Cchart CG
  obtain ⟨CprepC, CT, CR, Cterminal, Crem, -, hCT, -, -, -, hC⟩ :=
    (blockWordGeometry_of_package blockEdgePackage metricLetterFlux sourceLetterFlux :
      BlockWordGeometryStatement.{u, v, w, x, max u v}) D Ks Kmax Jchart Jm hchart hmol hKsJ Cm
      Cchart CG
  obtain ⟨Cenergy1, CTa, he1, hCTa, hO⟩ :=
    twoBlockJoint_old D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG CprepC CT CR Cterminal Crem hC
  obtain ⟨Cprep, hCprep, hfol⟩ :=
    following_actual_endpoint_energy.{u, v, w, x, max u v} D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cenergy1, Cprep, max CTa CT, he1, hCprep, le_max_of_le_left hCTa, fun n Npre hn => ?_⟩
  obtain ⟨Lpre, hLpre, hrPre, hWpre⟩ := hw Npre
  obtain ⟨-, -, -, hWn⟩ := hw n
  exact twoBlockMoment_body D Ks Kmax Jchart Jm hchart Cm Cchart CG CprepC CT CR Cterminal Crem
    hα0 hα1 hs0 hs1 hq hζ Cw Λ₀ h128 Cenergy1 CTa Cprep hO hfol n Npre hn Lpre hLpre hrPre hWpre
    hWn

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The prices of the two-block theorem, uniform over the family**.

These prices depend on the family through the source strength `θ = max Cth 0 · Θ ∈ [0, θmax]`
(`θmax = max Cth 0`, since `Θ ≤ 1`) and the strain `g ∈ [0, 1]`. Every factor is monotone in them
(the rank scale is explicit and monotone, `planeSourceRankScale_mono`; the response prices are
polynomials with nonnegative coefficients), so each price is at most its value at `θmax`, `g = 1`,
times the small factors `ζ^{2(Ks+1)} + (C_term ζ)^{2(J+1)}` (`ζ = R/E`) of the retained endpoints.

For `H = 0` the rank factors are `1`, and for `Θ = 0` one has `θ = 0`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

theorem terminalResponseEnergyPrice_mono {C C' : ℝ≥0∞} (hC : C ≤ C') (θ : ℝ≥0∞) (J H : ℕ) :
    terminalResponseEnergyPrice C θ J H ≤ terminalResponseEnergyPrice C' θ J H := by
  unfold terminalResponseEnergyPrice
  gcongr

theorem retainedResponseEnergyPrice_mono {C C' : ℝ≥0∞} (hC : C ≤ C') (θ : ℝ≥0∞) (J H : ℕ) :
    retainedResponseEnergyPrice C θ J H ≤ retainedResponseEnergyPrice C' θ J H := by
  unfold retainedResponseEnergyPrice
  gcongr with j _
  exact terminalResponseEnergyPrice_mono hC θ j H

theorem coupledRetainedResidualPrice_mono {C C' cm cm' cs cs' : ℝ≥0∞} (hC : C ≤ C')
    (hm : cm ≤ cm') (hs : cs ≤ cs') (ct : ℝ≥0∞) (J H : ℕ) :
    coupledRetainedResidualPrice C cm cs ct J H ≤ coupledRetainedResidualPrice C' cm' cs' ct J H := by
  unfold coupledRetainedResidualPrice
  gcongr
  · exact retainedResponseEnergyPrice_mono hC 1 J H
  · exact terminalResponseEnergyPrice_mono hC 1 J H

/-- The rank factor of a price at the source strength `θmax`. -/
theorem rankFactor_le.{u', v'} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D H : ℕ) {B B' : ℝ} (hB : 0 ≤ B)
    (hBB' : B ≤ B') :
    ENNReal.ofReal (planeSourceRankScale.{u', v'} n Kmax CG Cw D B ^ (2 * H)) ≤
      ENNReal.ofReal (planeSourceRankScale.{u', v'} n Kmax CG Cw D B' ^ (2 * H)) :=
  ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
    (zero_le_one.trans (one_le_planeSourceRankScale _ _ _ _ _ _))
    (planeSourceRankScale_mono _ _ _ _ _ hB hBB') _)

/-- The retained price at the source strength `θmax` and strain `1`, without its small factor. -/
def retainedConstant.{u', v'} (Cw : ℕ → ℝ) (Kmax D H : ℕ) (CG : ℕ → ℝ)
    (Cprep CR Crem θmax : ℝ) (n N L J : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((planeSourceRankScale.{u', v'} n Kmax (fun j => max (CG j) 0) Cw D
      (Cprep * θmax)) ^ (2 * H)) *
    (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u', v'} n Kmax (fun j => max (CG j) 0) Cw) *
      coupledRetainedResidualPrice
        (scalarResponseTwoInsertionCommonPrice Kmax (L : ℝ) Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Crem)) *
          (1 + ENNReal.ofReal θmax ^ 2))
        (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * CR ^ 2))
        (ENNReal.ofReal ((Crem * θmax) ^ 2))
        (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)) J H)

/-- The small factor of a retained endpoint. -/
def retainedSmall (ζ Ct : ℝ) (Ks J : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ζ ^ (2 * (Ks + 1)) + ENNReal.ofReal (Ct * ζ) ^ (2 * (J + 1))

/-- The small factor in powers of `E`. -/
theorem retainedSmall_le {ζ Ct Cl E c : ℝ} {Ks J : ℕ} (hζ0 : 0 ≤ ζ) (hζ : ζ ≤ Cl * E ^ c)
    (hCt : 0 ≤ Ct) (hE : 0 < E) (hE1 : E ≤ 1) (hc : 0 ≤ c) (hKJ : Ks ≤ J) :
    retainedSmall ζ Ct Ks J ≤
      ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Ct * Cl) ^ (2 * (J + 1))) *
        ENNReal.ofReal (E ^ (c * (2 * (Ks + 1) : ℕ))) := by
  have hEcp : 0 < E ^ c := Real.rpow_pos_of_pos hE c
  have hCl0 : 0 ≤ Cl := (mul_nonneg_iff_of_pos_right hEcp).1 (hζ0.trans hζ)
  have hEk : 0 ≤ E ^ (c * (2 * (Ks + 1) : ℕ)) := (Real.rpow_pos_of_pos hE _).le
  have h1 : ζ ^ (2 * (Ks + 1)) ≤ Cl ^ (2 * (Ks + 1)) * E ^ (c * (2 * (Ks + 1) : ℕ)) := by
    rw [← rpow_pow_eq hE, ← mul_pow]
    exact pow_le_pow_left₀ hζ0 hζ _
  have h3 : (Ct * ζ) ^ (2 * (J + 1)) ≤
      (Ct * Cl) ^ (2 * (J + 1)) * E ^ (c * (2 * (J + 1) : ℕ)) := by
    rw [← rpow_pow_eq hE, ← mul_pow, mul_assoc]
    exact pow_le_pow_left₀ (mul_nonneg hCt hζ0) (mul_le_mul_of_nonneg_left hζ hCt) _
  have hexp : c * ((2 * (Ks + 1) : ℕ) : ℝ) ≤ c * ((2 * (J + 1) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : 2 * (Ks + 1) ≤ 2 * (J + 1))) hc
  have h2 : (Ct * ζ) ^ (2 * (J + 1)) ≤ (Ct * Cl) ^ (2 * (J + 1)) *
      E ^ (c * (2 * (Ks + 1) : ℕ)) :=
    h3.trans (mul_le_mul_of_nonneg_left (rpow_mono_small hE hE1 hexp)
      (pow_nonneg (mul_nonneg hCt hCl0) _))
  have hA : 0 ≤ Cl ^ (2 * (Ks + 1)) + (Ct * Cl) ^ (2 * (J + 1)) := by positivity
  unfold retainedSmall
  rw [← ENNReal.ofReal_pow hζ0, ← ENNReal.ofReal_pow (mul_nonneg hCt hζ0),
    ← ENNReal.ofReal_add (pow_nonneg hζ0 _) (pow_nonneg (mul_nonneg hCt hζ0) _),
    ← ENNReal.ofReal_mul hA]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [h1, h2])

section Family

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The source strength of the premises lies in `[0, max Cth 0]`. -/
theorem JointPremisesGen.theta_bounds
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) :
    0 ≤ max Cth 0 * Θ ∧ max Cth 0 * Θ ≤ max Cth 0 :=
  ⟨mul_nonneg (le_max_right _ _) hp.hΘ₀,
    mul_le_of_le_one_right (le_max_right _ _) hp.hΘ₁⟩

/-- **A retained price is at most its uniform constant times its small factor.** -/
theorem twoRetained_le
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hg1 : g ≤ 1) (Cw : ℕ → ℝ) {Cprep CR Cterminal Crem : ℝ}
    (hCprep : 0 ≤ Cprep) (hCR : 0 ≤ CR) (hCt : 0 ≤ Cterminal) (hCrem : 0 ≤ Crem)
    (n N L J : ℕ) :
    twoRetained hp Cw Cprep CR Cterminal Crem n N L J ≤
      retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) n N L J *
        retainedSmall (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) Cterminal Ks J := by
  obtain ⟨hθ0, hθ1⟩ := hp.theta_bounds
  obtain ⟨hg0, -⟩ := hp.cov.g_range
  have hRE : 0 ≤ Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) :=
    div_nonneg (Real.sqrt_nonneg _) (Construction.Stream.ocEpsilon_pos hΛ).le
  have hM := metricTaylorUniformDensityPrice_nonneg Kmax
  have hrank := rankFactor_le.{u, v} n Kmax (fun j => max (CG j) 0) Cw D H
    (mul_nonneg hCprep hθ0) (mul_le_mul_of_nonneg_left hθ1 hCprep)
  have hcm : ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2) ≤
      ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * CR ^ 2) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hCR hg0)
      (mul_le_of_le_one_right hCR hg1) 2) hM)
  have hcs : ENNReal.ofReal ((Crem * (max Cth 0 * Θ)) ^ 2) ≤
      ENNReal.ofReal ((Crem * max Cth 0) ^ 2) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (mul_nonneg hCrem hθ0)
      (mul_le_mul_of_nonneg_left hθ1 hCrem) 2)
  have hC : scalarResponseTwoInsertionCommonPrice Kmax (L : ℝ) Cw N
        (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
        (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Crem)) *
        (1 + ENNReal.ofReal (max Cth 0 * Θ) ^ 2) ≤
      scalarResponseTwoInsertionCommonPrice Kmax (L : ℝ) Cw N
        (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
        (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Crem)) *
        (1 + ENNReal.ofReal (max Cth 0) ^ 2) :=
    mul_le_mul' le_rfl (add_le_add le_rfl (pow_le_pow_left₀ zero_le
      (ENNReal.ofReal_le_ofReal hθ1) 2))
  have hcr := coupledRetainedResidualPrice_mono hC hcm hcs
    (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)) J H
  have hη : ENNReal.ofReal (Cterminal * g *
      (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))) ^ (2 * (J + 1)) ≤
      ENNReal.ofReal (Cterminal *
        (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))) ^ (2 * (J + 1)) :=
    pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (by
      have := mul_nonneg hCt hRE
      nlinarith)) _
  unfold twoRetained retainedConstant retainedSmall
  refine (mul_le_mul' hrank (mul_le_mul' le_rfl (mul_le_mul' hcr
    (add_le_add le_rfl hη)))).trans (le_of_eq ?_)
  ring

/-- The energy price of a block at the source strength `θmax`. -/
def energyConstant.{u', v'} (Cw : ℕ → ℝ) (Kmax D H : ℕ) (CG : ℕ → ℝ) (Cenergy θmax : ℝ)
    (N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((planeSourceRankScale.{u', v'} N Kmax (fun j => max (CG j) 0) Cw D
      (Cenergy * θmax)) ^ (2 * H)) *
    (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u', v'} N Kmax (fun j => max (CG j) 0) Cw))

theorem twoCfirst_le
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Cw : ℕ → ℝ) {Cenergy : ℝ} (hCe : 0 ≤ Cenergy) (N : ℕ) :
    twoCfirst hp Cw Cenergy N ≤ energyConstant.{u, v} Cw Kmax D H CG Cenergy (max Cth 0) N := by
  obtain ⟨hθ0, hθ1⟩ := hp.theta_bounds
  unfold twoCfirst energyConstant
  exact mul_le_mul' (rankFactor_le.{u, v} N Kmax _ Cw D H (mul_nonneg hCe hθ0)
    (mul_le_mul_of_nonneg_left hθ1 hCe)) le_rfl

theorem twoCactual_le
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Cw : ℕ → ℝ) {Cenergy : ℝ} (hCe : 0 ≤ Cenergy) :
    twoCactual hp Cw Cenergy ≤ energyConstant.{u, v} Cw Kmax D H CG Cenergy (max Cth 0) 0 := by
  obtain ⟨hθ0, hθ1⟩ := hp.theta_bounds
  unfold twoCactual energyConstant
  exact mul_le_mul' (rankFactor_le.{u, v} 0 Kmax _ Cw D H (mul_nonneg hCe hθ0)
    (mul_le_mul_of_nonneg_left hθ1 hCe)) le_rfl

theorem twoMomentPrice_le
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Cw : ℕ → ℝ) {Cprep : ℝ} (hCp : 0 ≤ Cprep) (n : ℕ) :
    twoMomentPrice.{u, v} Cw Kmax D H CG Cprep (max Cth 0 * Θ) n ≤
      twoMomentPrice.{u, v} Cw Kmax D H CG Cprep (max Cth 0) n := by
  obtain ⟨hθ0, hθ1⟩ := hp.theta_bounds
  unfold twoMomentPrice
  exact mul_le_mul' (mul_le_mul' (rankFactor_le.{u, v} n Kmax _ Cw D H (mul_nonneg hCp hθ0)
    (mul_le_mul_of_nonneg_left hθ1 hCp)) le_rfl) le_rfl

/-- The uniform constant of the remaining price factor of the two-block theorem. -/
def c2RemainingConstant.{u', v'} (Cw : ℕ → ℝ) (Kmax D H Ks : ℕ) (CG : ℕ → ℝ)
    (Cenergy1 Cenergy2 Cprep CR Cterminal Crem θmax Cl : ℝ)
    (Npre Npost Lpre Lpost Jpre Jpost : ℕ) : ℝ≥0∞ :=
  2 * (energyConstant.{u', v'} Cw Kmax D H CG Cenergy2 θmax 0 *
      ENNReal.ofReal (cellTransitionMomentBudget Kmax 0) *
      ((retainedConstant.{u', v'} Cw Kmax D H CG Cprep CR Crem θmax Npost Npre Lpre Jpre *
          ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u', v'} Npre Kmax Cw)) *
        ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpre + 1)))) +
    ((retainedConstant.{u', v'} Cw Kmax D H CG Cprep CR Crem θmax 0 Npost Lpost Jpost *
          ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u', v'} Npost Kmax Cw) *
          ENNReal.ofReal (cellTransitionMomentBudget Kmax Npost)) *
        ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpost + 1)))) *
      (2 * (energyConstant.{u', v'} Cw Kmax D H CG Cenergy1 θmax Npre +
        (retainedConstant.{u', v'} Cw Kmax D H CG Cprep CR Crem θmax Npost Npre Lpre Jpre *
            ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u', v'} Npre Kmax Cw)) *
          ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpre + 1))))))

/-- **The remaining price factor of the two-block theorem in powers of `E`.** -/
theorem c2_remaining_le
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hg1 : g ≤ 1) (Cw : ℕ → ℝ)
    {Cenergy1 Cenergy2 Cprep CR Cterminal Crem : ℝ} (hCe1 : 0 ≤ Cenergy1) (hCe2 : 0 ≤ Cenergy2)
    (hCprep : 0 ≤ Cprep) (hCR : 0 ≤ CR) (hCt : 0 ≤ Cterminal) (hCrem : 0 ≤ Crem)
    (Npre Npost Lpre Lpost Jpre Jpost : ℕ) (hJpre : Ks ≤ Jpre) (hJpost : Ks ≤ Jpost)
    {Cl c : ℝ} (hc : 0 ≤ c) (hE1 : ocEpsilon q Λ (m - 1) ≤ 1)
    (hζ : Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) ≤
      Cl * ocEpsilon q Λ (m - 1) ^ c) :
    2 * (twoCactual hp Cw Cenergy2 * ENNReal.ofReal (cellTransitionMomentBudget Kmax 0) *
        twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre +
        twoEpsPost hp Cw Cprep CR Cterminal Crem Npost Lpost Jpost *
          (2 * (twoCfirst hp Cw Cenergy1 Npre +
            twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre))) ≤
      c2RemainingConstant.{u, v} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem
        (max Cth 0) Cl Npre Npost Lpre Lpost Jpre Jpost *
        ENNReal.ofReal (ocEpsilon q Λ (m - 1) ^ (c * (2 * (Ks + 1) : ℕ))) := by
  have hE := Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hζ0 : 0 ≤ Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) :=
    div_nonneg (Real.sqrt_nonneg _) hE.le
  have he1 : ENNReal.ofReal (ocEpsilon q Λ (m - 1) ^ (c * (2 * (Ks + 1) : ℕ))) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one hE.le hE1 (by positivity))
  have hspre := retainedSmall_le (Ct := Cterminal) hζ0 hζ hCt hE hE1 hc hJpre
  have hspost := retainedSmall_le (Ct := Cterminal) hζ0 hζ hCt hE hE1 hc hJpost
  have hpre : twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre ≤
      (retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) Npost Npre Lpre Jpre *
          ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npre Kmax Cw)) *
        (ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpre + 1))) *
          ENNReal.ofReal (ocEpsilon q Λ (m - 1) ^ (c * (2 * (Ks + 1) : ℕ)))) := by
    unfold twoEpsPre
    refine (mul_le_mul_left (twoRetained_le hp hΛ hg1 Cw hCprep hCR hCt hCrem Npost Npre Lpre
      Jpre) _).trans ?_
    exact (mul_right_comm _ _ _).trans_le (mul_le_mul_right hspre
      (retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) Npost Npre Lpre Jpre *
        ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npre Kmax Cw)))
  have hpost : twoEpsPost hp Cw Cprep CR Cterminal Crem Npost Lpost Jpost ≤
      (retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) 0 Npost Lpost Jpost *
          ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npost Kmax Cw) *
          ENNReal.ofReal (cellTransitionMomentBudget Kmax Npost)) *
        (ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpost + 1))) *
          ENNReal.ofReal (ocEpsilon q Λ (m - 1) ^ (c * (2 * (Ks + 1) : ℕ)))) := by
    unfold twoEpsPost
    refine (mul_le_mul_left (mul_le_mul_left (twoRetained_le hp hΛ hg1 Cw hCprep hCR hCt
      hCrem 0 Npost Lpost Jpost) _) _).trans ?_
    refine (le_of_eq ?_).trans (mul_le_mul_right hspost
      (retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) 0 Npost Lpost Jpost *
        ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npost Kmax Cw) *
        ENNReal.ofReal (cellTransitionMomentBudget Kmax Npost)))
    ring
  have hpre1 : twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre ≤
      (retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) Npost Npre Lpre Jpre *
          ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npre Kmax Cw)) *
        ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpre + 1))) :=
    hpre.trans (mul_le_mul_right (mul_le_of_le_one_right zero_le he1) _)
  have hCa := twoCactual_le hp Cw hCe2
  have hCf := twoCfirst_le hp Cw hCe1 Npre
  calc _ ≤ 2 * (energyConstant.{u, v} Cw Kmax D H CG Cenergy2 (max Cth 0) 0 *
          ENNReal.ofReal (cellTransitionMomentBudget Kmax 0) *
          ((retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) Npost Npre Lpre Jpre *
              ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npre Kmax Cw)) *
            (ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpre + 1))) *
              ENNReal.ofReal (ocEpsilon q Λ (m - 1) ^ (c * (2 * (Ks + 1) : ℕ))))) +
        ((retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) 0 Npost Lpost Jpost *
            ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npost Kmax Cw) *
            ENNReal.ofReal (cellTransitionMomentBudget Kmax Npost)) *
          (ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpost + 1))) *
            ENNReal.ofReal (ocEpsilon q Λ (m - 1) ^ (c * (2 * (Ks + 1) : ℕ))))) *
          (2 * (energyConstant.{u, v} Cw Kmax D H CG Cenergy1 (max Cth 0) Npre +
            (retainedConstant.{u, v} Cw Kmax D H CG Cprep CR Crem (max Cth 0) Npost Npre Lpre
                Jpre * ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npre Kmax Cw)) *
              ENNReal.ofReal (Cl ^ (2 * (Ks + 1)) + (Cterminal * Cl) ^ (2 * (Jpre + 1)))))) := by
        gcongr
    _ = _ := by
        unfold c2RemainingConstant
        ring

end Family

theorem energyConstant_ne_top.{u', v'} (Cw : ℕ → ℝ) (Kmax D H : ℕ) (CG : ℕ → ℝ)
    (Cenergy θmax : ℝ) (N : ℕ) : energyConstant.{u', v'} Cw Kmax D H CG Cenergy θmax N ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)

theorem retainedConstant_ne_top.{u', v'} (Cw : ℕ → ℝ) (Kmax D H : ℕ) (CG : ℕ → ℝ)
    (Cprep CR Crem θmax : ℝ) (n N L J : ℕ) :
    retainedConstant.{u', v'} Cw Kmax D H CG Cprep CR Crem θmax n N L J ≠ ⊤ := by
  unfold retainedConstant
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) ?_)
  refine coupledRetainedResidualPrice_ne_top _ _ _ _ ?_ ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top J H
  exact ENNReal.mul_ne_top (scalarResponseTwoInsertionCommonPrice_ne_top _ _ _ _ _ _
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.pow_ne_top ENNReal.ofReal_ne_top⟩)

theorem c2RemainingConstant_ne_top.{u', v'} (Cw : ℕ → ℝ) (Kmax D H Ks : ℕ) (CG : ℕ → ℝ)
    (Cenergy1 Cenergy2 Cprep CR Cterminal Crem θmax Cl : ℝ)
    (Npre Npost Lpre Lpost Jpre Jpost : ℕ) :
    c2RemainingConstant.{u', v'} Cw Kmax D H Ks CG Cenergy1 Cenergy2 Cprep CR Cterminal Crem θmax
      Cl Npre Npost Lpre Lpost Jpre Jpost ≠ ⊤ := by
  have h1 := energyConstant_ne_top.{u', v'} Cw Kmax D H CG Cenergy1 θmax Npre
  have h2 := energyConstant_ne_top.{u', v'} Cw Kmax D H CG Cenergy2 θmax 0
  have h3 := retainedConstant_ne_top.{u', v'} Cw Kmax D H CG Cprep CR Crem θmax Npost Npre Lpre
    Jpre
  have h4 := retainedConstant_ne_top.{u', v'} Cw Kmax D H CG Cprep CR Crem θmax 0 Npost Lpost
    Jpost
  unfold c2RemainingConstant
  finiteness

theorem twoMomentPrice_ne_top.{u', v'} (Cw : ℕ → ℝ) (Kmax D H : ℕ) (CG : ℕ → ℝ)
    (Cprep θ : ℝ) (n : ℕ) : twoMomentPrice.{u', v'} Cw Kmax D H CG Cprep θ n ≠ ⊤ := by
  unfold twoMomentPrice
  finiteness

end AVRegularity.CycleJointProofs.Assembly
end
end
