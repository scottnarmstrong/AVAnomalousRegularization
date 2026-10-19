-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.PiolaTested
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Coarse.Defect.Final
public import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
import AVRegularity.Weighted.MetricWordCoefficientArrayBound

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Time continuity in `H^K` from time continuity in `L²`.** A family `u t` of `ℤ²`-periodic
fields of class `C^{K+1}` whose ordered derivatives of orders `≤ K + 1` are bounded uniformly on a
time interval, and which is continuous in time into `L²` of the cell, is continuous in time into
`H^K` (`continuousOn_periodicHk_of_L2`). This is the interpolation
`‖∂_k h‖² = -∫⟪h, ∂_k∂_k h⟫ ≤ ‖h‖ ‖∂_k∂_k h‖` (periodic integration by parts,
`cellL2_partial_sq_le`) iterated over the letters of a word (`cellL2_orderedDerivative_le`). It
gives the clause `û ∈ C(I; H^K)` of the solution class for the physical
lift, whose `L²` continuity comes from its weak identity. -/

section Cell

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `L²` norm on the unit cell. -/
def cellL2 (f : Vec 2 → E) : ℝ := (eLpNorm f 2 (volume.restrict AVenhance.unitCube)).toReal

omit [InnerProductSpace ℝ E] in
theorem cellL2_nonneg (f : Vec 2 → E) : 0 ≤ cellL2 f := ENNReal.toReal_nonneg

/-- The cell pairing of an `L²` field with itself is the square of its `L²` norm. -/
theorem integral_inner_self_cell {f : Vec 2 → E}
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    ∫ x in AVenhance.unitCube, inner ℝ (f x) (f x) = cellL2 f ^ 2 := by
  have h := real_inner_self_eq_norm_sq (hf.toLp f)
  rw [MeasureTheory.L2.inner_def, Lp.norm_toLp] at h
  rw [cellL2, ← h]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

omit [InnerProductSpace ℝ E] in
/-- A field bounded by `C` has cell `L²` norm at most `C`: the cell has unit volume. -/
theorem cellL2_le_of_bound {f : Vec 2 → E}
    (hf : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C) : cellL2 f ≤ C := by
  have he := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict AVenhance.unitCube) hf
    (Eventually.of_forall hb)
  have he' : eLpNorm f 2 (volume.restrict AVenhance.unitCube) ≤ ENNReal.ofReal C := by
    simpa only [Measure.restrict_apply_univ, EntryWeakProofs.weak_unitCube_volume,
      ENNReal.one_rpow, one_mul] using he
  simpa only [cellL2, ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he'

/-- **Interpolation of one derivative** for a `C²` periodic field:
`‖∂_k g‖² ≤ ‖g‖ ‖∂_k∂_k g‖` in `L²` of the cell. -/
theorem cellL2_partial_sq_le {g : Vec 2 → E} (hg : ContDiff ℝ 2 g)
    (hp : AVenhance.IsZ2Periodic g) (k : Fin 2) :
    cellL2 (fun x => fderiv ℝ g x (basisVec k)) ^ 2 ≤
      cellL2 g *
        cellL2 (fun x => fderiv ℝ (fun y => fderiv ℝ g y (basisVec k)) x (basisVec k)) := by
  have hd1 : ContDiff ℝ 1 (fun x => fderiv ℝ g x (basisVec k)) :=
    (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  have M0 := Coarse.memLp_two_cell_of_continuous hg.continuous
  have M1 := Coarse.memLp_two_cell_of_continuous hd1.continuous
  have M2 := Coarse.memLp_two_cell_of_continuous (cell_continuous_partial hd1 k)
  have ibp := AVRegularity.CoupledEnergy.Variational.periodic_hilbert_partial_ibp g
    (fun x => fderiv ℝ g x (basisVec k)) (hg.of_le one_le_two) hd1 hp
    (AVRegularity.CycleComparison.Coarse.periodic_partial hp k) k
  calc cellL2 (fun x => fderiv ℝ g x (basisVec k)) ^ 2
      = ∫ x in AVenhance.unitCube,
          inner ℝ (fderiv ℝ g x (basisVec k)) (fderiv ℝ g x (basisVec k)) :=
        (integral_inner_self_cell M1).symm
    _ = -∫ x in AVenhance.unitCube, inner ℝ (g x)
          (fderiv ℝ (fun y => fderiv ℝ g y (basisVec k)) x (basisVec k)) := ibp
    _ ≤ |∫ x in AVenhance.unitCube, inner ℝ (g x)
          (fderiv ℝ (fun y => fderiv ℝ g y (basisVec k)) x (basisVec k))| := neg_le_abs _
    _ ≤ _ := Coarse.abs_integral_inner_le M0 M2

end Cell

/-! ### The interpolation modulus -/

/-- `Φ_0(δ) = δ`, `Φ_{j+1}(δ) = √(C Φ_j(δ))`. -/
def interpModulus (C : ℝ) : ℕ → ℝ → ℝ
  | 0, δ => δ
  | j + 1, δ => Real.sqrt (C * interpModulus C j δ)

theorem interpModulus_continuous (C : ℝ) : ∀ j, Continuous (interpModulus C j)
  | 0 => continuous_id
  | j + 1 => (continuous_const.mul (interpModulus_continuous C j)).sqrt

theorem interpModulus_zero (C : ℝ) : ∀ j, interpModulus C j 0 = 0
  | 0 => rfl
  | j + 1 => by
      show Real.sqrt (C * interpModulus C j 0) = 0
      rw [interpModulus_zero C j, mul_zero, Real.sqrt_zero]

section Words

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Interpolation of the ordered derivatives.** If the ordered derivatives of orders `≤ j + 1`
of a `C^{j+1}` periodic field have cell `L²` norms at most `C`, those of order `j` are at most
`Φ_j` of the `L²` norm of the field. -/
theorem cellL2_orderedDerivative_le {C : ℝ} (hC : 0 ≤ C) :
    ∀ (j : ℕ) (g : Vec 2 → E), ContDiff ℝ ((j + 1 : ℕ) : ℕ∞) g → AVenhance.IsZ2Periodic g →
      (∀ i, i ≤ j + 1 → ∀ w : DerivativeWord2 i, cellL2 (orderedDerivative w g) ≤ C) →
      ∀ β : DerivativeWord2 j, cellL2 (orderedDerivative β g) ≤ interpModulus C j (cellL2 g)
  | 0, g, _, _, _, β => by
      rw [orderedDerivative_zero g β]
      exact le_rfl
  | j + 1, g, hg, hp, hb, β => by
      set β' : DerivativeWord2 j := fun i => β i.castSucc with hβ'
      set k : Fin 2 := β (Fin.last j) with hk
      have hh : ContDiff ℝ 2 (orderedDerivative β' g) := by
        have h2 := ChartTransport.contDiff_orderedDerivative (p := 2) β'
          (hg.of_le (by exact_mod_cast (show 2 + j ≤ j + 1 + 1 by omega)))
        exact_mod_cast h2
      have hhp := ChartTransport.isZ2Periodic_orderedDerivative β' hp
      have e1 : orderedDerivative β g =
          fun x => fderiv ℝ (orderedDerivative β' g) x (basisVec k) := orderedDerivative_succ β g
      have e2 : orderedDerivative (Fin.snoc β k : DerivativeWord2 (j + 1 + 1)) g =
          fun x => fderiv ℝ (fun y => fderiv ℝ (orderedDerivative β' g) y (basisVec k)) x
            (basisVec k) := by
        rw [orderedDerivative_succ (Fin.snoc β k : DerivativeWord2 (j + 1 + 1)) g]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [e1]
      have hB := cellL2_partial_sq_le hh hhp k
      have hih := cellL2_orderedDerivative_le hC j g
        (hg.of_le (by exact_mod_cast Nat.le_succ (j + 1)))
        hp (fun i hi w => hb i (Nat.le_succ_of_le hi) w) β'
      have h2 : cellL2 (fun x => fderiv ℝ (fun y => fderiv ℝ (orderedDerivative β' g) y
          (basisVec k)) x (basisVec k)) ≤ C := by
        rw [← e2]
        exact hb (j + 1 + 1) le_rfl _
      have hΦ0 : 0 ≤ interpModulus C j (cellL2 g) := (cellL2_nonneg _).trans hih
      have hsq : cellL2 (orderedDerivative β g) ^ 2 ≤ C * interpModulus C j (cellL2 g) := by
        rw [e1]
        refine hB.trans ?_
        rw [mul_comm C]
        exact mul_le_mul hih h2 (cellL2_nonneg _) hΦ0
      calc cellL2 (orderedDerivative β g)
          = Real.sqrt (cellL2 (orderedDerivative β g) ^ 2) :=
            (Real.sqrt_sq (cellL2_nonneg _)).symm
        _ ≤ Real.sqrt (C * interpModulus C j (cellL2 g)) := Real.sqrt_le_sqrt hsq

end Words

section Trajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- The norm of the difference of two carriers is at most the sum of the cell `L²` norms of the
ordered derivatives of the difference of the fields. -/
theorem periodicHk_sub_norm_le (K : ℕ) {f g : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hg : ContDiff ℝ (K : ℕ∞) g) (hfp : AVenhance.IsZ2Periodic f)
    (hgp : AVenhance.IsZ2Periodic g) :
    ‖periodicHk K f hf hfp - periodicHk K g hg hgp‖ ≤
      ∑ a : JetIndex2 K, cellL2 (orderedDerivative a.2 (fun x => f x - g x)) := by
  refine (AVRegularity.Weighted.finitePiLp_norm_le_sum
    (periodicHk K f hf hfp - periodicHk K g hg hgp).val).trans (Finset.sum_le_sum fun a _ => ?_)
  have hcoe : (periodicHk K f hf hfp - periodicHk K g hg hgp).val a =
      (periodicHk K f hf hfp).val a - (periodicHk K g hg hgp).val a := rfl
  have hle : a.1.val ≤ K := Nat.lt_succ_iff.1 a.1.isLt
  have hsub := orderedDerivative_sub a.2 (hf.of_le (by exact_mod_cast hle))
    (hg.of_le (by exact_mod_cast hle))
  rw [hcoe, Lp.norm_def, cellL2, hsub]
  refine le_of_eq (congrArg ENNReal.toReal (eLpNorm_congr_ae ?_))
  filter_upwards [Lp.coeFn_sub ((periodicHk K f hf hfp).val a) ((periodicHk K g hg hgp).val a),
    periodicHk_jet_ae K f hf hfp a, periodicHk_jet_ae K g hg hgp a] with x hx hfx hgx
  rw [hx, Pi.sub_apply, hfx, hgx]

/-- **Time continuity in `H^K` from time continuity in `L²`** and uniform bounds of the ordered
derivatives of orders `≤ K + 1`. -/
theorem continuousOn_periodicHk_of_L2 (K : ℕ) (u : ℝ → Vec 2 → E) {t₀ t₁ : ℝ}
    (hu : ∀ t, ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (u t)) (hp : ∀ t, AVenhance.IsZ2Periodic (u t))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ Set.Icc t₀ t₁, ∀ i, i ≤ K + 1 → ∀ (w : DerivativeWord2 i) (x : Vec 2),
      ‖orderedDerivative w (u t) x‖ ≤ C)
    (hL2 : ∀ t ∈ Set.Icc t₀ t₁, Tendsto (fun s => cellL2 (fun x => u s x - u t x))
      (𝓝[Set.Icc t₀ t₁] t) (𝓝 0)) :
    ContinuousOn (fun t => periodicHk K (u t)
      ((hu t).of_le (by exact_mod_cast Nat.le_succ K)) (hp t)) (Set.Icc t₀ t₁) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hK : ∀ t, ContDiff ℝ (K : ℕ∞) (u t) := fun t =>
    (hu t).of_le (by exact_mod_cast Nat.le_succ K)
  -- the bound of every ordered derivative of a difference
  have hdiff : ∀ s ∈ Set.Icc t₀ t₁, ∀ i, i ≤ K + 1 → ∀ w : DerivativeWord2 i,
      cellL2 (orderedDerivative w (fun x => u s x - u t x)) ≤ 2 * C := by
    intro s hs i hi w
    have hsi : ContDiff ℝ (i : ℕ∞) (u s) := (hu s).of_le (by exact_mod_cast hi)
    have hti : ContDiff ℝ (i : ℕ∞) (u t) := (hu t).of_le (by exact_mod_cast hi)
    rw [orderedDerivative_sub w hsi hti]
    refine cellL2_le_of_bound ?_ (by positivity) fun x => ?_
    · exact ((ChartTransport.continuous_orderedDerivative w hsi).sub
        (ChartTransport.continuous_orderedDerivative w hti)).aestronglyMeasurable
    · refine (norm_sub_le _ _).trans ?_
      have h1 := hb s hs i hi w x
      have h2 := hb t ht i hi w x
      linarith
  -- the squeeze
  have hlim : Tendsto (fun s => ∑ a : JetIndex2 K,
      interpModulus (2 * C) a.1.val (cellL2 (fun x => u s x - u t x)))
      (𝓝[Set.Icc t₀ t₁] t) (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ a : JetIndex2 K, interpModulus (2 * C) a.1.val 0 := by
      simp only [interpModulus_zero, Finset.sum_const_zero]
    rw [h0]
    exact tendsto_finsetSum _ fun a _ =>
      ((interpModulus_continuous (2 * C) a.1.val).tendsto 0).comp (hL2 t ht)
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  refine (periodicHk_sub_norm_le K (hK s) (hK t) (hp s) (hp t)).trans
    (Finset.sum_le_sum fun a _ => ?_)
  have hle : a.1.val ≤ K := Nat.lt_succ_iff.1 a.1.isLt
  refine cellL2_orderedDerivative_le (by positivity) a.1.val (fun x => u s x - u t x)
    (((hu s).sub (hu t)).of_le (by exact_mod_cast Nat.succ_le_succ hle))
    (fun n x => by
      show u s (x + AVenhance.latticeShift n) - u t (x + AVenhance.latticeShift n) =
        u s x - u t x
      rw [hp s n x, hp t n x])
    (fun i hi w => hdiff s hs i (hi.trans (Nat.succ_le_succ hle)) w) a.2

end Trajectory

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Carriers of fields that may fail to be smooth**. `carrierOf K f` is the torus
Sobolev carrier `periodicHk K f` when `f` is of class `C^K` and `ℤ²`-periodic, and `0` otherwise
(`carrierOf_eq`): this defines carrier families of the residuals of the Galerkin approximants at
every time, without reference to the window hypotheses. The carrier of a difference is the
difference of the carriers (`periodicHk_sub`, `carrierOf_sub`). -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The carrier of a difference is the difference of the carriers.** -/
theorem periodicHk_sub (K : ℕ) {f g : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hg : ContDiff ℝ (K : ℕ∞) g) (hfp : AVenhance.IsZ2Periodic f)
    (hgp : AVenhance.IsZ2Periodic g) :
    periodicHk K f hf hfp - periodicHk K g hg hgp =
      periodicHk K (fun x => f x - g x) (hf.sub hg) (fun n x => by
        show f (x + AVenhance.latticeShift n) - g (x + AVenhance.latticeShift n) = f x - g x
        rw [hfp n x, hgp n x]) := by
  apply Subtype.ext
  ext a : 1
  have hcoe : (periodicHk K f hf hfp - periodicHk K g hg hgp).val a =
      (periodicHk K f hf hfp).val a - (periodicHk K g hg hgp).val a := rfl
  rw [hcoe]
  have hle : a.1.val ≤ K := Nat.lt_succ_iff.1 a.1.isLt
  have hsub := orderedDerivative_sub a.2 (hf.of_le (by exact_mod_cast hle))
    (hg.of_le (by exact_mod_cast hle))
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub ((periodicHk K f hf hfp).val a) ((periodicHk K g hg hgp).val a),
    periodicHk_jet_ae K f hf hfp a, periodicHk_jet_ae K g hg hgp a,
    periodicHk_jet_ae K (fun x => f x - g x) (hf.sub hg) (fun n x => by
      show f (x + AVenhance.latticeShift n) - g (x + AVenhance.latticeShift n) = f x - g x
      rw [hfp n x, hgp n x]) a] with x hx hfx hgx hdx
  rw [hx, Pi.sub_apply, hfx, hgx, hdx, hsub]

open scoped Classical in
/-- The carrier of a field: `periodicHk K f` when `f` is `C^K` and periodic, `0` otherwise. -/
def carrierOf (K : ℕ) (f : Vec 2 → E) : TorusHk K E :=
  if h : ContDiff ℝ (K : ℕ∞) f ∧ AVenhance.IsZ2Periodic f then periodicHk K f h.1 h.2 else 0

/-- The carrier of a smooth periodic field. -/
theorem carrierOf_eq (K : ℕ) {f : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) : carrierOf K f = periodicHk K f hf hp := by
  classical
  unfold carrierOf
  simp only [hf, hp, and_self, ↓reduceDIte]

/-- **The carrier of a difference of smooth periodic fields.** -/
theorem carrierOf_sub (K : ℕ) {f g : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hg : ContDiff ℝ (K : ℕ∞) g) (hfp : AVenhance.IsZ2Periodic f)
    (hgp : AVenhance.IsZ2Periodic g) :
    carrierOf K f - carrierOf K g = carrierOf K (fun x => f x - g x) := by
  rw [carrierOf_eq K hf hfp, carrierOf_eq K hg hgp, periodicHk_sub K hf hg hfp hgp,
    carrierOf_eq K (hf.sub hg) (fun n x => by
      show f (x + AVenhance.latticeShift n) - g (x + AVenhance.latticeShift n) = f x - g x
      rw [hfp n x, hgp n x])]

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open Filter Topology
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Weak identities against first-order tests from smooth tests.** A `CoupledWeakIdentity` on
the unit cell that holds for every smooth periodic test holds for every `TorusHk 1` test
(`coupledWeakIdentity_of_smooth`), provided the drift is bounded and measurable, the initial and
final values are `L²`, and the gradient, flux, forcing and source are `L²` on the cell at every
time with a bound integrable in time. Both sides of the identity are bounded linear in the test,
the time integrand by an integrable function of time (`weakRhs_integrable_and_bound`), and the
Galerkin projections of a first-order field are smooth periodic approximants converging to it, so
the identity passes to the limit (`integrated_identity_of_tendsto_dom`). -/

/-- **Density extension of an integrated identity with an integrable bound.** As
`Coarse.integrated_identity_of_tendsto`, with the uniform bound of the time integrand replaced by
a bound `M s ‖φ‖` with `M` integrable on `(t₀,t]`. -/
theorem integrated_identity_of_tendsto_dom {X : Type*} [SeminormedAddCommGroup X]
    {t₀ t : ℝ} (L : X → ℝ) (R : ℝ → X → ℝ)
    (hLsub : ∀ φ φ', L (φ - φ') = L φ - L φ') {c : ℝ} (hLb : ∀ φ, |L φ| ≤ c * ‖φ‖)
    (hRsub : ∀ s ∈ Set.Ioc t₀ t, ∀ φ φ', R s (φ - φ') = R s φ - R s φ') {M : ℝ → ℝ}
    (hM : IntegrableOn M (Set.Ioc t₀ t)) (hRb : ∀ s ∈ Set.Ioc t₀ t, ∀ φ, |R s φ| ≤ M s * ‖φ‖)
    {φ : X} {φN : ℕ → X} (hconv : Tendsto φN atTop (𝓝 φ))
    (hN : ∀ n, IntegrableOn (fun s => R s (φN n)) (Set.Ioc t₀ t) ∧
      L (φN n) = ∫ s in Set.Ioc t₀ t, R s (φN n)) :
    IntegrableOn (fun s => R s φ) (Set.Ioc t₀ t) ∧ L φ = ∫ s in Set.Ioc t₀ t, R s φ := by
  have hM' : Integrable M (volume.restrict (Set.Ioc t₀ t)) := hM
  have hdist : Tendsto (fun n => ‖φN n - φ‖) atTop (𝓝 0) := by
    simpa [dist_eq_norm] using (tendsto_iff_dist_tendsto_zero.1 hconv)
  have hdiff : ∀ s ∈ Set.Ioc t₀ t, ∀ n, ‖R s (φN n) - R s φ‖ ≤ M s * ‖φN n - φ‖ :=
    fun s hs n => by
      rw [Real.norm_eq_abs, ← hRsub s hs]
      exact hRb s hs _
  -- pointwise convergence of the right sides
  have hpt : ∀ s ∈ Set.Ioc t₀ t, Tendsto (fun n => R s (φN n)) atTop (𝓝 (R s φ)) := by
    intro s hs
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (hdiff s hs)
      (by simpa only [mul_zero] using hdist.const_mul (M s))
  -- the limit right side is integrable
  have hmeas : AEStronglyMeasurable (fun s => R s φ) (volume.restrict (Set.Ioc t₀ t)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hN n).1.aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hpt))
  have hint : IntegrableOn (fun s => R s φ) (Set.Ioc t₀ t) :=
    (hM'.mul_const ‖φ‖).mono' hmeas
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs]; exact hRb s hs φ))
  refine ⟨hint, ?_⟩
  -- convergence of both sides
  have hL : Tendsto (fun n => L (φN n)) atTop (𝓝 (L φ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hdist.const_mul |c|)
    rw [Real.norm_eq_abs, ← hLsub]
    exact (hLb _).trans (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _))
  have hI : Tendsto (fun n => ∫ s in Set.Ioc t₀ t, R s (φN n)) atTop
      (𝓝 (∫ s in Set.Ioc t₀ t, R s φ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n => (∫ s in Set.Ioc t₀ t, M s) * ‖φN n - φ‖)
      (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa only [mul_zero] using hdist.const_mul (∫ s in Set.Ioc t₀ t, M s))
    rw [← integral_sub (hN n).1 hint]
    have h1 : ‖∫ s in Set.Ioc t₀ t, R s (φN n) - R s φ‖ ≤
        ∫ s in Set.Ioc t₀ t, M s * ‖φN n - φ‖ :=
      norm_integral_le_of_norm_le (hM'.mul_const ‖φN n - φ‖)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs =>
          hdiff s hs n))
    exact h1.trans_eq (integral_mul_const _ _)
  exact tendsto_nhds_unique hL (hI.congr fun n => ((hN n).2).symm)

section Integrand

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The time integrand of `CoupledWeakIdentity` for a test `φ` with gradient `dφ`. -/
def weakRhs (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H) (φ : Vec 2 → H)
    (dφ : Fin 2 → Vec 2 → H) (s : ℝ) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
    - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
    - ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (dφ k x)
    + inner ℝ (g s x) (φ x)

/-- `CoupledWeakIdentity` written with the named time integrand `weakRhs`. -/
theorem coupledWeakIdentity_iff {μ : Measure (Vec 2)} {ν t₀ t : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {u₀ f φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du : ℝ → Fin 2 → Vec 2 → H}
    {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H} :
    CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F g ↔
      Integrable (fun x => inner ℝ (u₀ x) (φ x)) μ ∧
      Integrable (fun x => inner ℝ (f x) (φ x)) μ ∧
      (∀ s ∈ Set.Ioc t₀ t, Integrable (weakRhs ν v du flux F g φ dφ s) μ) ∧
      IntegrableOn (fun s => ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ) (Set.Ioc t₀ t) ∧
      ∫ x, inner ℝ (u₀ x) (φ x) ∂μ - ∫ x, inner ℝ (f x) (φ x) ∂μ
        = ∫ s in Set.Ioc t₀ t, ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ :=
  Iff.rfl

/-- **The time integrand at one time.** With a bounded measurable drift and `L²` gradient, flux,
forcing and source bounded by `c`, the integrand tested with `L²` fields `φ`, `dφ` bounded by
`Mφ` is integrable, and its integral is bounded by `(2 Vb + 2|ν| + 5) c Mφ`. -/
theorem weakRhs_integrable_and_bound {μ : Measure (Vec 2)} {ν : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {du : ℝ → Fin 2 → Vec 2 → H} {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)}
    {g : ℝ → Vec 2 → H} {s Vb c : ℝ} (hvm : ∀ k, AEStronglyMeasurable (fun x => v s x k) μ)
    (hv : ∀ x k, |v s x k| ≤ Vb)
    (hdu : ∀ k, MemLp (du s k) 2 μ ∧ (eLpNorm (du s k) 2 μ).toReal ≤ c)
    (hflux : ∀ k, MemLp (fun x => flux s x k) 2 μ ∧
      (eLpNorm (fun x => flux s x k) 2 μ).toReal ≤ c)
    (hF : ∀ k, MemLp (fun x => F s x k) 2 μ ∧ (eLpNorm (fun x => F s x k) 2 μ).toReal ≤ c)
    (hg : MemLp (g s) 2 μ ∧ (eLpNorm (g s) 2 μ).toReal ≤ c)
    {φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {Mφ : ℝ} (hφ : MemLp φ 2 μ)
    (hφb : (eLpNorm φ 2 μ).toReal ≤ Mφ) (hdφ : ∀ k, MemLp (dφ k) 2 μ)
    (hdφb : ∀ k, (eLpNorm (dφ k) 2 μ).toReal ≤ Mφ) :
    Integrable (weakRhs ν v du flux F g φ dφ s) μ ∧
      |∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ| ≤ (2 * Vb + 2 * |ν| + 5) * c * Mφ := by
  have hc : 0 ≤ c := ENNReal.toReal_nonneg.trans hg.2
  have hZ : ∀ k, MemLp (fun x => flux s x k + F s x k) 2 μ ∧
      (eLpNorm (fun x => flux s x k + F s x k) 2 μ).toReal ≤ 2 * c := fun k => by
    obtain ⟨m1, b1⟩ := hflux k
    obtain ⟨m2, b2⟩ := hF k
    refine ⟨m1.add m2, ?_⟩
    refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨m1.eLpNorm_lt_top.ne,
      m2.eLpNorm_lt_top.ne⟩) (eLpNorm_add_le (by norm_num))).trans ?_
    rw [ENNReal.toReal_add m1.eLpNorm_lt_top.ne m2.eLpNorm_lt_top.ne]
    linarith
  obtain ⟨hI, hb⟩ := Coarse.weakIntegrand_integrable_and_bound (bk := fun k x => v s x k) hvm
    (fun k x => hv x k) ν (fun k => (hdu k).1) (fun k => (hdu k).2) (fun k => (hZ k).1)
    (fun k => (hZ k).2) hφ hφb hdφ hdφb
  have hgI : Integrable (fun x => inner ℝ (g s x) (φ x)) μ := Coarse.integrable_inner_memLp hg.1 hφ
  have hgb : |∫ x, inner ℝ (g s x) (φ x) ∂μ| ≤ c * Mφ :=
    (Coarse.abs_integral_inner_le hg.1 hφ).trans
      (mul_le_mul hg.2 hφb ENNReal.toReal_nonneg hc)
  have hI' : Integrable (weakRhs ν v du flux F g φ dφ s) μ := hI.add hgI
  have hsplit : ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ =
      (∫ x, Coarse.weakIntegrand (fun k x => v s x k) ν (du s)
        (fun k x => flux s x k + F s x k) φ dφ x ∂μ) + ∫ x, inner ℝ (g s x) (φ x) ∂μ :=
    integral_add hI hgI
  refine ⟨hI', ?_⟩
  rw [hsplit]
  refine (abs_add_le _ _).trans ((add_le_add hb hgb).trans_eq ?_)
  ring

end Integrand

section Torus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] [CompleteSpace H]

/-- The time integrand of `CoupledWeakIdentity` tested with a first-order periodic field: the
test is its value jet and the gradient its first-order jets. -/
def testRhs (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (ψ : TorusHk 1 H) (s : ℝ) : Vec 2 → ℝ :=
  weakRhs ν v du flux F g (ψ.toFunction.jet (valueIndex2 1))
    (fun k => ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) s

/-- The tested time integrand is subtractive in the test. -/
theorem testRhs_sub (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (ψ ψ' : TorusHk 1 H) (s : ℝ) :
    testRhs ν v du flux F g (ψ - ψ') s =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => testRhs ν v du flux F g ψ s x - testRhs ν v du flux F g ψ' s x := by
  filter_upwards [Coarse.jet_sub_ae ψ ψ'] with x hx
  simp only [testRhs, weakRhs, hx, inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  ring

/-- On Galerkin approximants the tested time integrand is the smooth time integrand. -/
theorem testRhs_galerkin_ae [FiniteDimensional ℝ H] (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (du : ℝ → Fin 2 → Vec 2 → H) (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H) (n : ℕ) (φ : TorusHk 1 H) (s : ℝ) :
    testRhs ν v du flux F g (galerkinProj n φ) s =ᵐ[volume.restrict AVenhance.unitCube]
      weakRhs ν v du flux F g (Coarse.approxField n φ)
        (fun k x => fderiv ℝ (Coarse.approxField n φ) x (basisVec k)) s := by
  filter_upwards [Coarse.galerkin_value_ae n φ, Coarse.galerkin_deriv_ae n φ 0,
    Coarse.galerkin_deriv_ae n φ 1] with x h0 hd0 hd1
  have hdk : ∀ k : Fin 2,
      (galerkinProj n φ).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x
        = fderiv ℝ (Coarse.approxField n φ) x (basisVec k) := fun k => by
    fin_cases k
    exacts [hd0, hd1]
  simp only [testRhs, weakRhs, h0, hdk]

/-- **Weak identities against first-order tests from smooth tests.** On the unit cell, let the
drift be measurable and bounded by `Vb`, let `u₀, f ∈ L²`, and let the gradient `du s k`, the flux
and forcing components and the source `g s` be `L²` with `L²` norms at most `C s` for
`s ∈ (t₀,t]`, where `C` is integrable on `(t₀,t]`. If the `CoupledWeakIdentity` holds for every
smooth `ℤ²`-periodic test (with its classical gradient), it holds for every `TorusHk 1` test (with
its value and first-order jets). -/
theorem coupledWeakIdentity_of_smooth [FiniteDimensional ℝ H] (ν t₀ t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (Vb : ℝ)
    (hvm : ∀ s ∈ Set.Ioc t₀ t, ∀ k,
      AEStronglyMeasurable (fun x => v s x k) (volume.restrict AVenhance.unitCube))
    (hv : ∀ s ∈ Set.Ioc t₀ t, ∀ x k, |v s x k| ≤ Vb)
    (u₀ f : Vec 2 → H) (hu₀ : MemLp u₀ 2 (volume.restrict AVenhance.unitCube))
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (du : ℝ → Fin 2 → Vec 2 → H) (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H) (C : ℝ → ℝ) (hC : IntegrableOn C (Set.Ioc t₀ t))
    (hdu : ∀ s ∈ Set.Ioc t₀ t, ∀ k, MemLp (du s k) 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (du s k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hflux : ∀ s ∈ Set.Ioc t₀ t, ∀ k,
      MemLp (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hF : ∀ s ∈ Set.Ioc t₀ t, ∀ k,
      MemLp (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hg : ∀ s ∈ Set.Ioc t₀ t, MemLp (g s) 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (g s) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hsmooth : ∀ φ : Vec 2 → H, ContDiff ℝ (⊤ : ℕ∞) φ → AVenhance.IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν t₀ t v u₀ f φ
        (fun k x => fderiv ℝ φ x (basisVec k)) du flux F g)
    (φ : TorusHk 1 H) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν t₀ t v u₀ f
      (φ.toFunction.jet (valueIndex2 1))
      (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) du flux F g := by
  -- the two sides of the identity as functions of the test
  let Lf : TorusHk 1 H → ℝ := fun ψ =>
    (∫ x in AVenhance.unitCube, inner ℝ (u₀ x) (ψ.toFunction.jet (valueIndex2 1) x)) -
      ∫ x in AVenhance.unitCube, inner ℝ (f x) (ψ.toFunction.jet (valueIndex2 1) x)
  let Rf : ℝ → TorusHk 1 H → ℝ := fun s ψ =>
    ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ s x
  have hB : ∀ s ∈ Set.Ioc t₀ t, ∀ ψ : TorusHk 1 H,
      Integrable (testRhs ν v du flux F g ψ s) (volume.restrict AVenhance.unitCube) ∧
        |Rf s ψ| ≤ (2 * Vb + 2 * |ν| + 5) * C s * ‖ψ‖ := fun s hs ψ =>
    weakRhs_integrable_and_bound (hvm s hs) (hv s hs) (hdu s hs) (hflux s hs) (hF s hs)
      (hg s hs) (Coarse.memLp_jet ψ (valueIndex2 1)) (Coarse.eLpNorm_jet_le ψ (valueIndex2 1))
      (fun k => Coarse.memLp_jet ψ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
      (fun k => Coarse.eLpNorm_jet_le ψ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
  have hLsub : ∀ ψ ψ', Lf (ψ - ψ') = Lf ψ - Lf ψ' := fun ψ ψ' => by
    simp only [Lf]
    rw [Coarse.integral_inner_jet_sub hu₀ ψ ψ', Coarse.integral_inner_jet_sub hf ψ ψ']
    ring
  have hLb : ∀ ψ : TorusHk 1 H, |Lf ψ| ≤
      ((eLpNorm u₀ 2 (volume.restrict AVenhance.unitCube)).toReal +
        (eLpNorm f 2 (volume.restrict AVenhance.unitCube)).toReal) * ‖ψ‖ := fun ψ => by
    simp only [Lf]
    refine (abs_sub _ _).trans ?_
    rw [add_mul]
    exact add_le_add
      ((Coarse.abs_integral_inner_le hu₀ (Coarse.memLp_jet ψ _)).trans
        (mul_le_mul_of_nonneg_left (Coarse.eLpNorm_jet_le ψ _) ENNReal.toReal_nonneg))
      ((Coarse.abs_integral_inner_le hf (Coarse.memLp_jet ψ _)).trans
        (mul_le_mul_of_nonneg_left (Coarse.eLpNorm_jet_le ψ _) ENNReal.toReal_nonneg))
  have hRsub : ∀ s ∈ Set.Ioc t₀ t, ∀ ψ ψ', Rf s (ψ - ψ') = Rf s ψ - Rf s ψ' :=
    fun s hs ψ ψ' => by
      simp only [Rf]
      rw [integral_congr_ae (testRhs_sub ν v du flux F g ψ ψ' s)]
      exact integral_sub (hB s hs ψ).1 (hB s hs ψ').1
  have hRb : ∀ s ∈ Set.Ioc t₀ t, ∀ ψ, |Rf s ψ| ≤ (2 * Vb + 2 * |ν| + 5) * C s * ‖ψ‖ :=
    fun s hs ψ => (hB s hs ψ).2
  -- the identity for the Galerkin approximants
  have hN : ∀ n, IntegrableOn (fun s => Rf s (galerkinProj n φ)) (Set.Ioc t₀ t) ∧
      Lf (galerkinProj n φ) = ∫ s in Set.Ioc t₀ t, Rf s (galerkinProj n φ) := fun n => by
    obtain ⟨-, -, -, hI, heq⟩ := coupledWeakIdentity_iff.1
      (hsmooth _ (Coarse.approxField_contDiff n φ) (Coarse.approxField_periodic n φ))
    have hR' : (fun s => Rf s (galerkinProj n φ)) = fun s =>
        ∫ x in AVenhance.unitCube, weakRhs ν v du flux F g (Coarse.approxField n φ)
          (fun k x => fderiv ℝ (Coarse.approxField n φ) x (basisVec k)) s x :=
      funext fun s => integral_congr_ae (testRhs_galerkin_ae ν v du flux F g n φ s)
    have hL' : Lf (galerkinProj n φ) =
        (∫ x in AVenhance.unitCube, inner ℝ (u₀ x) (Coarse.approxField n φ x)) -
          ∫ x in AVenhance.unitCube, inner ℝ (f x) (Coarse.approxField n φ x) := by
      simp only [Lf]
      congr 1
      · refine integral_congr_ae ?_
        filter_upwards [Coarse.galerkin_value_ae n φ] with x hx
        rw [hx]
      · refine integral_congr_ae ?_
        filter_upwards [Coarse.galerkin_value_ae n φ] with x hx
        rw [hx]
    rw [hR', hL']
    exact ⟨hI, heq⟩
  have hKC : IntegrableOn (fun s => (2 * Vb + 2 * |ν| + 5) * C s) (Set.Ioc t₀ t) :=
    Integrable.const_mul hC _
  obtain ⟨hI, heq⟩ := integrated_identity_of_tendsto_dom Lf Rf hLsub hLb hRsub hKC hRb
    (galerkinProj_tendsto φ) hN
  exact coupledWeakIdentity_iff.2
    ⟨Coarse.integrable_inner_memLp hu₀ (Coarse.memLp_jet φ _),
      Coarse.integrable_inner_memLp hf (Coarse.memLp_jet φ _), fun s hs => (hB s hs φ).1, hI,
      heq⟩

end Torus

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Limits of weak identities.** The time integrand of `CoupledWeakIdentity` (`weakRhs`) is
linear in the gradient, the flux, the forcing and the source. If these converge in `L²` of the
cell at every time, with a bound of the four differences whose time integral tends to zero, the
time integrals of the tested integrands converge (`tendsto_weakRhs_integral`); hence a family of
weak identities whose end values also converge passes to the limit
(`coupledWeakIdentity_of_tendsto`). This is the passage from the finite-rank approximants of the
coarse field to the coarse field in the reconstruction. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The time integrand of the weak identity is linear in the gradient, flux, forcing and
source. -/
theorem weakRhs_sub (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (du du' : ℝ → Fin 2 → Vec 2 → H)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g g' : ℝ → Vec 2 → H)
    (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H) (s : ℝ) (x : Vec 2) :
    weakRhs ν v (fun s k x => du s k x - du' s k x) (fun s x => flux s x - flux' s x)
        (fun s x => F s x - F' s x) (fun s x => g s x - g' s x) φ dφ s x =
      weakRhs ν v du flux F g φ dφ s x - weakRhs ν v du' flux' F' g' φ dφ s x := by
  simp only [weakRhs, inner_sub_left, inner_add_left, PiLp.sub_apply, mul_sub,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- **The tested integrands of two data at one time** differ by at most
`(2 V_b + 2|ν| + 5) c M_φ`, when the four differences of the data are bounded in `L²` by `c`. -/
theorem abs_weakRhs_integral_sub_le {μ : Measure (Vec 2)} {ν : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {Vb : ℝ} {s : ℝ} (hvm : ∀ k, AEStronglyMeasurable (fun x => v s x k) μ)
    (hv : ∀ x k, |v s x k| ≤ Vb)
    {du du' : ℝ → Fin 2 → Vec 2 → H} {flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)}
    {g g' : ℝ → Vec 2 → H} {φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {Mφ c : ℝ}
    (hφ : MemLp φ 2 μ) (hφb : (eLpNorm φ 2 μ).toReal ≤ Mφ) (hdφ : ∀ k, MemLp (dφ k) 2 μ)
    (hdφb : ∀ k, (eLpNorm (dφ k) 2 μ).toReal ≤ Mφ)
    (hdu : ∀ k, MemLp (fun x => du' s k x - du s k x) 2 μ ∧
      (eLpNorm (fun x => du' s k x - du s k x) 2 μ).toReal ≤ c)
    (hflux : ∀ k, MemLp (fun x => (flux' s x - flux s x) k) 2 μ ∧
      (eLpNorm (fun x => (flux' s x - flux s x) k) 2 μ).toReal ≤ c)
    (hF : ∀ k, MemLp (fun x => (F' s x - F s x) k) 2 μ ∧
      (eLpNorm (fun x => (F' s x - F s x) k) 2 μ).toReal ≤ c)
    (hg : MemLp (fun x => g' s x - g s x) 2 μ ∧
      (eLpNorm (fun x => g' s x - g s x) 2 μ).toReal ≤ c)
    (hI' : Integrable (weakRhs ν v du' flux' F' g' φ dφ s) μ)
    (hI : Integrable (weakRhs ν v du flux F g φ dφ s) μ) :
    |(∫ x, weakRhs ν v du' flux' F' g' φ dφ s x ∂μ) - ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ| ≤
      (2 * Vb + 2 * |ν| + 5) * c * Mφ := by
  have hb := (weakRhs_integrable_and_bound (ν := ν)
    (du := fun s k x => du' s k x - du s k x) (flux := fun s x => flux' s x - flux s x)
    (F := fun s x => F' s x - F s x) (g := fun s x => g' s x - g s x) hvm hv
    hdu hflux hF hg hφ hφb hdφ hdφb).2
  have he : (∫ x, weakRhs ν v du' flux' F' g' φ dφ s x ∂μ) -
      ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ =
      ∫ x, weakRhs ν v (fun s k x => du' s k x - du s k x)
        (fun s x => flux' s x - flux s x) (fun s x => F' s x - F s x)
        (fun s x => g' s x - g s x) φ dφ s x ∂μ := by
    rw [← integral_sub hI' hI]
    exact integral_congr_ae (Eventually.of_forall fun x => (weakRhs_sub ν v _ _ _ _ _ _ _ _ φ dφ
      s x).symm)
  rw [he]
  exact hb

/-- **Convergence of the tested time integrals.** -/
theorem tendsto_weakRhs_integral {μ : Measure (Vec 2)} {ν t₀ t : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {Vb : ℝ} (hvm : ∀ s ∈ Set.Ioc t₀ t, ∀ k, AEStronglyMeasurable (fun x => v s x k) μ)
    (hv : ∀ s ∈ Set.Ioc t₀ t, ∀ x k, |v s x k| ≤ Vb)
    {du : ℝ → Fin 2 → Vec 2 → H} {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)}
    {g : ℝ → Vec 2 → H} {duM : ℕ → ℝ → Fin 2 → Vec 2 → H}
    {fluxM FM : ℕ → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {gM : ℕ → ℝ → Vec 2 → H}
    {φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {Mφ : ℝ} (hφ : MemLp φ 2 μ)
    (hφb : (eLpNorm φ 2 μ).toReal ≤ Mφ) (hdφ : ∀ k, MemLp (dφ k) 2 μ)
    (hdφb : ∀ k, (eLpNorm (dφ k) 2 μ).toReal ≤ Mφ) (c : ℕ → ℝ → ℝ)
    (hc : ∀ M, IntegrableOn (c M) (Set.Ioc t₀ t))
    (hc0 : Tendsto (fun M => ∫ s in Set.Ioc t₀ t, c M s) atTop (𝓝 0))
    (hdu : ∀ M, ∀ s ∈ Set.Ioc t₀ t, ∀ k, MemLp (fun x => duM M s k x - du s k x) 2 μ ∧
      (eLpNorm (fun x => duM M s k x - du s k x) 2 μ).toReal ≤ c M s)
    (hflux : ∀ M, ∀ s ∈ Set.Ioc t₀ t, ∀ k,
      MemLp (fun x => (fluxM M s x - flux s x) k) 2 μ ∧
        (eLpNorm (fun x => (fluxM M s x - flux s x) k) 2 μ).toReal ≤ c M s)
    (hF : ∀ M, ∀ s ∈ Set.Ioc t₀ t, ∀ k, MemLp (fun x => (FM M s x - F s x) k) 2 μ ∧
      (eLpNorm (fun x => (FM M s x - F s x) k) 2 μ).toReal ≤ c M s)
    (hg : ∀ M, ∀ s ∈ Set.Ioc t₀ t, MemLp (fun x => gM M s x - g s x) 2 μ ∧
      (eLpNorm (fun x => gM M s x - g s x) 2 μ).toReal ≤ c M s)
    (hIM : ∀ M, ∀ s ∈ Set.Ioc t₀ t,
      Integrable (weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ dφ s) μ)
    (hI : ∀ s ∈ Set.Ioc t₀ t, Integrable (weakRhs ν v du flux F g φ dφ s) μ)
    (hTM : ∀ M, IntegrableOn
      (fun s => ∫ x, weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ dφ s x ∂μ) (Set.Ioc t₀ t))
    (hT : IntegrableOn (fun s => ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ) (Set.Ioc t₀ t)) :
    Tendsto (fun M => ∫ s in Set.Ioc t₀ t,
        ∫ x, weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ dφ s x ∂μ) atTop
      (𝓝 (∫ s in Set.Ioc t₀ t, ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ)) := by
  -- the difference of the integrands at one time
  have hpt : ∀ M, ∀ s ∈ Set.Ioc t₀ t,
      |(∫ x, weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ dφ s x ∂μ) -
        ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ| ≤ (2 * Vb + 2 * |ν| + 5) * c M s * Mφ :=
    fun M s hs => abs_weakRhs_integral_sub_le (hvm s hs) (hv s hs) hφ hφb hdφ hdφb (hdu M s hs)
      (hflux M s hs) (hF M s hs) (hg M s hs) (hIM M s hs) (hI s hs)
  -- the difference of the time integrals
  have hbound : ∀ M, ‖(∫ s in Set.Ioc t₀ t,
        ∫ x, weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ dφ s x ∂μ) -
      ∫ s in Set.Ioc t₀ t, ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ‖ ≤
      (2 * Vb + 2 * |ν| + 5) * Mφ * ∫ s in Set.Ioc t₀ t, c M s := by
    intro M
    rw [← integral_sub (hTM M) hT, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hc M).const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs]
    refine (hpt M s hs).trans_eq ?_
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun M => norm_nonneg _) hbound ?_
  simpa using hc0.const_mul ((2 * Vb + 2 * |ν| + 5) * Mφ)

/-- **A family of weak identities passes to the limit** when the end pairings and the tested time
integrals converge and the limit integrands are integrable. -/
theorem coupledWeakIdentity_of_tendsto {μ : Measure (Vec 2)} {ν t₀ t : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {u₀ f φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H}
    {du : ℝ → Fin 2 → Vec 2 → H} {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)}
    {g : ℝ → Vec 2 → H} {u₀M fM : ℕ → Vec 2 → H} {duM : ℕ → ℝ → Fin 2 → Vec 2 → H}
    {fluxM FM : ℕ → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {gM : ℕ → ℝ → Vec 2 → H}
    (hM : ∀ M, CoupledWeakIdentity μ ν t₀ t v (u₀M M) (fM M) φ dφ (duM M) (fluxM M) (FM M)
      (gM M))
    (hu₀ : Integrable (fun x => inner ℝ (u₀ x) (φ x)) μ)
    (hf : Integrable (fun x => inner ℝ (f x) (φ x)) μ)
    (hI : ∀ s ∈ Set.Ioc t₀ t, Integrable (weakRhs ν v du flux F g φ dφ s) μ)
    (hT : IntegrableOn (fun s => ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ) (Set.Ioc t₀ t))
    (hlimu : Tendsto (fun M => ∫ x, inner ℝ (u₀M M x) (φ x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (u₀ x) (φ x) ∂μ)))
    (hlimf : Tendsto (fun M => ∫ x, inner ℝ (fM M x) (φ x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (f x) (φ x) ∂μ)))
    (hlimR : Tendsto (fun M => ∫ s in Set.Ioc t₀ t,
        ∫ x, weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ dφ s x ∂μ) atTop
      (𝓝 (∫ s in Set.Ioc t₀ t, ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ))) :
    CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F g := by
  refine coupledWeakIdentity_iff.2 ⟨hu₀, hf, hI, hT, ?_⟩
  refine tendsto_nhds_unique (hlimu.sub hlimf) ?_
  have he : ∀ M, (∫ x, inner ℝ (u₀M M x) (φ x) ∂μ) - ∫ x, inner ℝ (fM M x) (φ x) ∂μ =
      ∫ s in Set.Ioc t₀ t, ∫ x, weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ dφ s x ∂μ :=
    fun M => (coupledWeakIdentity_iff.1 (hM M)).2.2.2.2
  simpa only [he] using hlimR

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Splitting the tested right side of a weak identity**. When the flux residual
is a sum of three fluxes and the forcing a sum of four forcings, each tested piece integrable on
the cell, the cell integral of the tested right side `weakRhs` is the corresponding signed sum of
the cell integrals of the pieces (`integral_weakRhs_split`). This is the bookkeeping that turns the
finite-rank identity of the glued lift into a weak identity with an explicit residual
presentation. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The tested right side with a three-piece flux and a four-piece forcing.** -/
theorem integral_weakRhs_split {μ : Measure (Vec 2)} (ν : ℝ) (b : ℝ → Vec 2 → Vec 2)
    (du : ℝ → Fin 2 → Vec 2 → H) (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (F1 F2 F3 : Vec 2 → Fin 2 → H) (g1 g2 g3 g4 : Vec 2 → H) (φ : Vec 2 → H)
    (dφ : Fin 2 → Vec 2 → H) (s : ℝ)
    (hb : Integrable (fun x => ∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x)) μ)
    (hd : Integrable (fun x => ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)) μ)
    (he : Integrable (fun x => ∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x)) μ)
    (hF1 : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x)) μ)
    (hF2 : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x)) μ)
    (hF3 : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x)) μ)
    (hg1 : Integrable (fun x => inner ℝ (g1 x) (φ x)) μ)
    (hg2 : Integrable (fun x => inner ℝ (g2 x) (φ x)) μ)
    (hg3 : Integrable (fun x => inner ℝ (g3 x) (φ x)) μ)
    (hg4 : Integrable (fun x => inner ℝ (g4 x) (φ x)) μ) :
    ∫ x, weakRhs ν b du flux
        (fun _ x => WithLp.toLp 2 (fun k => F1 x k + F2 x k + F3 x k))
        (fun _ x => g1 x + g2 x + g3 x + g4 x) φ dφ s x ∂μ =
      -(∫ x, ∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x) ∂μ)
        - ν * (∫ x, ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x) ∂μ)
        - (∫ x, ∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x) ∂μ)
        - (∫ x, ∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x) ∂μ)
        - (∫ x, ∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x) ∂μ)
        - (∫ x, ∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x) ∂μ)
        + (∫ x, inner ℝ (g1 x) (φ x) ∂μ) + (∫ x, inner ℝ (g2 x) (φ x) ∂μ)
        + (∫ x, inner ℝ (g3 x) (φ x) ∂μ) + (∫ x, inner ℝ (g4 x) (φ x) ∂μ) := by
  have hpt : ∀ x, weakRhs ν b du flux
      (fun _ x => WithLp.toLp 2 (fun k => F1 x k + F2 x k + F3 x k))
      (fun _ x => g1 x + g2 x + g3 x + g4 x) φ dφ s x =
      -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
        - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
        - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))
        - (∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x))
        - (∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x))
        - (∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x))
        + inner ℝ (g1 x) (φ x) + inner ℝ (g2 x) (φ x)
        + inner ℝ (g3 x) (φ x) + inner ℝ (g4 x) (φ x) := by
    intro x
    have hk : ∀ k : Fin 2, inner ℝ (flux s x k +
        (WithLp.toLp 2 (fun k => F1 x k + F2 x k + F3 x k) : PiLp 2 (fun _ : Fin 2 => H)) k)
        (dφ k x) = inner ℝ (flux s x k) (dφ k x) + inner ℝ (F1 x k) (dφ k x) +
          inner ℝ (F2 x k) (dφ k x) + inner ℝ (F3 x k) (dφ k x) := fun k => by
      show inner ℝ (flux s x k + (F1 x k + F2 x k + F3 x k)) (dφ k x) = _
      simp only [inner_add_left]
      ring
    simp only [weakRhs, hk, Finset.sum_add_distrib, inner_add_left]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have j1 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))) μ := hb.neg
  have j2 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
      - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))) μ := j1.sub (hd.const_mul ν)
  have j3 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
      - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))) μ := j2.sub he
  have j4 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
      - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x))) μ := j3.sub hF1
  have j5 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
      - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x))) μ := j4.sub hF2
  have j6 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
      - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x))) μ := j5.sub hF3
  have j7 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
      - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x))
      + inner ℝ (g1 x) (φ x)) μ := j6.add hg1
  have j8 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
      - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x))
      + inner ℝ (g1 x) (φ x) + inner ℝ (g2 x) (φ x)) μ := j7.add hg2
  have j9 : Integrable (fun x => -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
      - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x))
      - (∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x))
      + inner ℝ (g1 x) (φ x) + inner ℝ (g2 x) (φ x) + inner ℝ (g3 x) (φ x)) μ := j8.add hg3
  rw [integral_add j9 hg4, integral_add j8 hg3, integral_add j7 hg2, integral_add j6 hg1,
    integral_sub j5 hF3, integral_sub j4 hF2, integral_sub j3 hF1, integral_sub j2 he,
    integral_sub j1 (hd.const_mul ν), integral_neg, integral_const_mul]

/-- The tested right side with a three-piece flux and a four-piece forcing is integrable when
every tested piece is. -/
theorem integrable_weakRhs_split {μ : Measure (Vec 2)} (ν : ℝ) (b : ℝ → Vec 2 → Vec 2)
    (du : ℝ → Fin 2 → Vec 2 → H) (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (F1 F2 F3 : Vec 2 → Fin 2 → H) (g1 g2 g3 g4 : Vec 2 → H) (φ : Vec 2 → H)
    (dφ : Fin 2 → Vec 2 → H) (s : ℝ)
    (hb : Integrable (fun x => ∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x)) μ)
    (hd : Integrable (fun x => ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)) μ)
    (he : Integrable (fun x => ∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x)) μ)
    (hF1 : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x)) μ)
    (hF2 : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x)) μ)
    (hF3 : Integrable (fun x => ∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x)) μ)
    (hg1 : Integrable (fun x => inner ℝ (g1 x) (φ x)) μ)
    (hg2 : Integrable (fun x => inner ℝ (g2 x) (φ x)) μ)
    (hg3 : Integrable (fun x => inner ℝ (g3 x) (φ x)) μ)
    (hg4 : Integrable (fun x => inner ℝ (g4 x) (φ x)) μ) :
    Integrable (fun x => weakRhs ν b du flux
        (fun _ x => WithLp.toLp 2 (fun k => F1 x k + F2 x k + F3 x k))
        (fun _ x => g1 x + g2 x + g3 x + g4 x) φ dφ s x) μ := by
  have hpt : ∀ x, weakRhs ν b du flux
      (fun _ x => WithLp.toLp 2 (fun k => F1 x k + F2 x k + F3 x k))
      (fun _ x => g1 x + g2 x + g3 x + g4 x) φ dφ s x =
      -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φ x))
        - ν * (∑ k : Fin 2, inner ℝ (du s k x) (dφ k x))
        - (∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))
        - (∑ k : Fin 2, inner ℝ (F1 x k) (dφ k x))
        - (∑ k : Fin 2, inner ℝ (F2 x k) (dφ k x))
        - (∑ k : Fin 2, inner ℝ (F3 x k) (dφ k x))
        + inner ℝ (g1 x) (φ x) + inner ℝ (g2 x) (φ x)
        + inner ℝ (g3 x) (φ x) + inner ℝ (g4 x) (φ x) := by
    intro x
    have hk : ∀ k : Fin 2, inner ℝ (flux s x k +
        (WithLp.toLp 2 (fun k => F1 x k + F2 x k + F3 x k) : PiLp 2 (fun _ : Fin 2 => H)) k)
        (dφ k x) = inner ℝ (flux s x k) (dφ k x) + inner ℝ (F1 x k) (dφ k x) +
          inner ℝ (F2 x k) (dφ k x) + inner ℝ (F3 x k) (dφ k x) := fun k => by
      show inner ℝ (flux s x k + (F1 x k + F2 x k + F3 x k)) (dφ k x) = _
      simp only [inner_add_left]
      ring
    simp only [weakRhs, hk, Finset.sum_add_distrib, inner_add_left]
    ring
  have h := (((((((((hb.neg.sub (hd.const_mul ν)).sub he).sub hF1).sub hF2).sub hF3).add
    hg1).add hg2).add hg3).add hg4)
  exact h.congr (Filter.Eventually.of_forall fun x => (hpt x).symm)

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Weak identities from tested time identities.** If the cell pairing `t ↦ ∫⟪u(t), φ⟫` is of
integral type on `[t_A, t_Z]` (`IsPrimOn`) with a density that is, at the times of `(t_A, t_Z]`,
the cell integral of the tested right side `weakRhs`, then the integrated weak identity
(`CoupledWeakIdentity`) from `t_A` holds at every time of the interval
(`coupledWeakIdentity_of_isPrimOn`). This is the converse of `isPrimOn_of_coupledWeakIdentity`;
it puts the tested identity of the glued lift in the form of
the solution class. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Weak identities from tested time identities.** -/
theorem coupledWeakIdentity_of_isPrimOn {μ : Measure (Vec 2)} {ν tA tZ : ℝ}
    (v : ℝ → Vec 2 → Vec 2) (u : ℝ → Vec 2 → H) (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H) (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H) (dens : ℝ → ℝ)
    (hprim : IsPrimOn tA tZ (fun t => ∫ x, inner ℝ (u t x) (φ x) ∂μ) dens)
    (hdens : ∀ s ∈ Ioc tA tZ, dens s = ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ)
    (hu : ∀ t ∈ Icc tA tZ, Integrable (fun x => inner ℝ (u t x) (φ x)) μ)
    (hI : ∀ s ∈ Ioc tA tZ, Integrable (weakRhs ν v du flux F g φ dφ s) μ) :
    ∀ t ∈ Icc tA tZ, CoupledWeakIdentity μ ν tA t v (u t) (u tA) φ dφ du flux F g := by
  intro t ht
  have htAZ : tA ≤ tZ := ht.1.trans ht.2
  have hsub : Ioc tA t ⊆ Ioc tA tZ := Ioc_subset_Ioc_right ht.2
  have hdi : IntegrableOn dens (Ioc tA t) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le htAZ).1 hprim.1).mono_set hsub
  have heq : EqOn dens (fun s => ∫ x, weakRhs ν v du flux F g φ dφ s x ∂μ) (Ioc tA t) :=
    fun s hs => hdens s (hsub hs)
  refine coupledWeakIdentity_iff.2 ⟨hu t ht, hu tA ⟨le_rfl, htAZ⟩, fun s hs => hI s (hsub hs),
    hdi.congr_fun heq measurableSet_Ioc, ?_⟩
  have h := hprim.2 t ht
  rw [intervalIntegral.integral_of_le ht.1, setIntegral_congr_fun measurableSet_Ioc heq] at h
  linarith

end AVRegularity.CycleComparison.Reconstruction
end
