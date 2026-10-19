-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.RawCopyPaths
import AVRegularity.CycleComparison.Error.Main
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Actual finite-route defect pricing with the SAME native full path,
buffered datum and raw descending-copy solution. Whole-window charts are
replaced by the real Eulerian coefficient hypotheses and its Schur budget;
local-to-global sampling supplies those hypotheses. The fixed-point/restart
and the expansion consumers are already proved. The degenerate cases are included: H=0 has no
defect; empty and singleton types, D=2, constants, zero data, identity geometry, an
edgeless seed and a point post-buffer window retain precisely these maps.
No independent solution or mass-dependent map is chosen. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace preparationNeutralEnergyAdd preparationNeutralEnergyMonoid
  preparationNeutralEnergyModule
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}


/-- The generic physical moment price from the proved selected-copy
dissipation and the same two scalar rows and higher classes. -/
theorem raw_moment_price_of_dissipation
    (family : ChartedFamily ι h D Part Ctx) {H : ℕ} (ν ρ a b : ℝ)
    (Pq : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) a b ρ ν 0 D)
    (P : PreparationPlainKernelFrame Pq) (v : ℝ → Vec 2 → Vec 2) (Kmax : ℕ)
    (hd : TorusDriftData ν ρ a b v Kmax) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (q S L d : ℝ) (hq : 0 ≤ q) (hL : 0 ≤ L) (hd0 : 0 ≤ d)
    (hw : ∀ i j γ, (P.spec i j γ).width ≤ q * ρ)
    (hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * P.rows.basePrice i j))
    (V : ∀ j, ℝ → TorusHk (P.K j + 1) (h j))
    (hV : ∀ j, MemLp (V j) 2 (volume.restrict (Set.Icc a b)))
    (zp zk : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b a)
    (wp wk : ∀ i, ℝ → TorusHk 1 (h i))
    (hp : ∀ i, IsTorusForcedRow ν a b v 2 0 0
      (P.rows.plainSourceFluxTime V i) (fun _ => 0)
      (fun t => zp.1 (Set.projIcc a b Pq.htime t) i) (wp i))
    (hk : ∀ i, IsTorusForcedRow ν a b v 2 0 0
      (Pq.carrierFlux (fun j t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (P.K j)))
        (V j t)) i) (fun _ => 0)
      (fun t => zk.1 (Set.projIcc a b Pq.htime t) i) (wk i))
    (hwp : zp.2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i => wp i t))
    (hwk : zk.2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i => wk i t))
    (hdiss : ν * (∫ t in Set.Icc a b, massGradNormSq ρ π (fun j => (V j t).val)) ≤
      (4 * L ^ (2 * H)) * d) :
    preparationWeightedPathEnergy (h := h) ρ π ν a b a (zp - zk) ≤
      14 * (q ^ P.L * |S| / ν) * L ^ H * Real.sqrt d := by
  have hint := CycleComparison.Error.integrable_massGradNormSq ρ π V hV
  have he := P.source_difference_path_energy hd π hπ q S hq hw hs V
    (fun j => (hV j).aestronglyMeasurable) hint (fun _ => 0) zp zk wp wk hp hk hwp hwk
  have hX : 0 ≤ ∫ t in Set.Icc a b, massGradNormSq ρ π (fun j => (V j t).val) :=
    integral_nonneg fun t => massGradNormSq_nonneg ρ π hπ _
  exact he.trans (raw_defect_sqrt_cost Pq.diffusivity_pos hX hd0 hL
    (mul_nonneg (pow_nonneg hq _) (abs_nonneg S)) hdiss)

/-- Exact Eulerian and Schur hypotheses of the supplied raw copy system. -/
structure RawCopyBounds (family : ChartedFamily ι h D Part Ctx)
    (H Kbase Kmax : ℕ) (ν ρ c b e Esc : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (π : ι → ℝ) (actual : ∀ p, Ctx p) (Sr : ℝ) : Prop where
  order_bound : ∀ x : ι × Fin (H + 1), preparationNeutralSlots H D Kbase x ≤ Kmax
  order_ge_two : 2 ≤ D
  drift : TorusDriftData ν ρ c b
      v Kmax
  budget_nonneg : 0 ≤ Sr
  schur : SchurBound Sr
      (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
        (preparationNeutralSlots H D Kbase) D c b
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase)))
  finite : ∀ x y d, coefficientSeminorm ρ
      (preparationNeutralSlots H D Kbase x) c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d) ≠ ⊤
  measurable : ∀ x y d, Measurable (fun p : Set.Icc c b × Vec 2 =>
      edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d p.1 p.2)
  smooth : ∀ x y d t, t ∈ Set.Icc c b → ContDiff ℝ
      (preparationNeutralSlots H D Kbase x : ℕ)
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t)
  periodic : ∀ x y d t, t ∈ Set.Icc c b → IsZ2Periodic
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t)

/-- One fixed raw copied solution and step have the exact physical moment
price. Linear datum evaluation is left to the final wrapper. -/
theorem raw_selected_step_price
    (family : ChartedFamily ι h D Part Ctx)
    (H Kbase Kmax : ℕ)
    (ν ρ c b e Esc : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (π : ι → ℝ)
    (_hπ : ∀ i, 0 < π i)
    (actual : ∀ p, Ctx p)
    (l : Fin H)
    (f : ∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i))
    (u : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1))
    (W : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x + 1) (h x.1))
    (hsol : IsCoupledWeakSolutionTorus ν c b v D (preparationNeutralSlots H D Kbase)
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase))
      (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) f)
      (fun _ _ => 0) (fun _ _ => 0) u W)
    (zp zprev : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (htrace : ∀ t : Set.Icc c b, zp.1 t = fun i =>
      truncateTorusHk (Nat.zero_le _) (u (i, l.succ) t))
    (hclass : zp.2 =ᵐ[volume.restrict (Set.Icc c b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i =>
        truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l.succ) t)))
    (hprev : zprev.2 =ᵐ[volume.restrict (Set.Icc c b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i =>
        truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l.castSucc) t)))
    (Pq : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) c b ρ ν 0 D)
    (P : PreparationPlainKernelFrame Pq)
    (_hcoeff : ∀ i j γ d, Pq.B i j γ d =
      constituentPhysical family ν e Esc actual i j γ d.val)
    (_hincl : ∀ i j γ, Pq.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (J : CoupledHighTime (h := h) (fun _ => 0) c b →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hsource : ScalarFamilyEnergyPathRealizes (ν := ν) Pq.htime
      v (preparationKernelScalarDatum Pq) J)
    (_hreserve : ∀ j, P.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (q S Sr : ℝ)
    (_hq : 0 ≤ q)
    (_hw : ∀ i j γ, (P.spec i j γ).width ≤ q * ρ)
    (_hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * P.rows.basePrice i j))
    (R : RawCopyBounds family H Kbase Kmax ν ρ c b e Esc v π actual Sr) :
    preparationWeightedPathEnergy (h := h) ρ π ν c b c (zp - J zprev.2) ≤
      14 * (q ^ P.L * |S| / ν) * (8 * Sr + 1) ^ H *
        Real.sqrt (massNormSq ρ π (fun i => (f i).val)) := by
  classical
  let Kc : ι × Fin (H + 1) → ℕ := preparationNeutralSlots H D Kbase
  let fc := preparationNeutralInitial H Kc f
  let L := 8 * Sr + 1
  have hdiss := raw_solution_copy_dissipation Kc P.K l.castSucc (_hreserve)
    Kmax R.order_bound ν ρ c b v Pq.diffusivity_pos Pq.radius_pos Pq.htime R.drift R.order_ge_two π _hπ
    (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual Kc)
    R.finite R.measurable R.smooth R.periodic
    (fun x y d hxy t _ => congrFun
      (raw_neutral_edge_zero family H ν e Esc actual Kc x y d hxy) t)
    Sr R.budget_nonneg R.schur fc u W hsol
  let V : ∀ j, ℝ → TorusHk (P.K j + 1) (h j) :=
    preparationNeutralPrecedingInput P l (_hreserve) W
  have hV : ∀ j, MemLp (V j) 2 (volume.restrict (Set.Icc c b)) :=
    fun j => truncate_memLp (Nat.succ_le_succ (_hreserve j)) (hsol.2.1 (j, l.castSucc))
  have hrows := neutral_selected_step_rows P l (_hreserve) e Esc actual _hcoeff _hincl
    v J _hsource f u W hsol zp zprev
    htrace hprev
  let Zk := Classical.choose hrows.2
  have hk := (Classical.choose_spec hrows.2).1
  have hZk := (Classical.choose_spec hrows.2).2
  have hL : 0 ≤ L := add_nonneg (mul_nonneg (by norm_num) R.budget_nonneg) zero_le_one
  have hp := raw_moment_price_of_dissipation family ν ρ c b Pq P v Kmax R.drift π _hπ
    q S L (massNormSq ρ (fun x => π x.1) (fun x => (fc x).val)) _hq hL
    (massNormSq_nonneg ρ (fun x => π x.1) (fun x => _hπ x.1) (fun x => (fc x).val))
    _hw _hs V hV zp (J zprev.2)
    (fun i t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l.succ) t))
    Zk hrows.1 hk hclass hZk hdiss
  change _ ≤ 14 * (q ^ P.L * |S| / ν) * L ^ H *
    Real.sqrt (massNormSq ρ (fun x => π x.1)
      (fun x => (preparationNeutralInitial H Kc f x).val)) at hp
  rw [raw_injected_mass] at hp
  exact hp


theorem raw_post_buffer_price
    (family : ChartedFamily ι h D Part Ctx)
    (H Kbase Kmax : ℕ)
    (ν ρ c b e Esc : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (π : ι → ℝ)
    (_hπ : ∀ i, 0 < π i)
    (actual : ∀ p, Ctx p)
    (_Kbound : ∀ x : ι × Fin (H + 1), preparationNeutralSlots H D Kbase x ≤ Kmax)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (u : (∀ i, TorusHk 0 (h i)) →
      ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1))
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase)
      ν c b e Esc v actual B u E)
    (Pq : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) c b ρ ν 0 D)
    (P : PreparationPlainKernelFrame Pq)
    (_hcoeff : ∀ i j γ d, Pq.B i j γ d =
      constituentPhysical family ν e Esc actual i j γ d.val)
    (_hincl : ∀ i j γ, Pq.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (J : CoupledHighTime (h := h) (fun _ => 0) c b →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hsource : ScalarFamilyEnergyPathRealizes (ν := ν) Pq.htime
      v (preparationKernelScalarDatum Pq) J)
    (_hD : 2 ≤ D)
    (_hd : TorusDriftData ν ρ c b
      v Kmax)
    (_hreserve : ∀ (l : Fin H) j, P.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (q S Sr : ℝ)
    (_hq : 0 ≤ q)
    (_hSr : 0 ≤ Sr)
    (_hw : ∀ i j γ, (P.spec i j γ).width ≤ q * ρ)
    (_hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * P.rows.basePrice i j))
    (_hraw_schur : SchurBound Sr
      (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
        (preparationNeutralSlots H D Kbase) D c b
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))))
    (_hfinite : ∀ x y d, coefficientSeminorm ρ
      (preparationNeutralSlots H D Kbase x) c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d) ≠ ⊤)
    (_hmeas : ∀ x y d, Measurable (fun p : Set.Icc c b × Vec 2 =>
      edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d p.1 p.2))
    (_hsmooth : ∀ x y d t, t ∈ Set.Icc c b → ContDiff ℝ
      (preparationNeutralSlots H D Kbase x : ℕ)
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hper : ∀ x y d t, t ∈ Set.Icc c b → IsZ2Periodic
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t)) :
    RawPostPriceStatement H P.L (fun i => preparationNeutralSlots H D Kbase (i, 0))
      ρ ν c b q S Sr π B J E := by
  intro f l
  obtain ⟨W, hs, ht, hW⟩ := _hreal f
  let R : RawCopyBounds family H Kbase Kmax ν ρ c b e Esc v π actual Sr :=
    ⟨_Kbound, _hD, _hd, _hSr, _hraw_schur, _hfinite, _hmeas, _hsmooth, _hper⟩
  exact raw_selected_step_price family H Kbase Kmax ν ρ c b e Esc v π _hπ actual
    l (B f) (u f) W hs (E l.succ f) (E l.castSucc f) (ht l.succ) (hW l.succ) (hW l.castSucc)
    Pq P _hcoeff _hincl J _hsource (_hreserve l) q S Sr _hq _hw _hs R
end

/-! Actual finite-route defect pricing with the SAME native full path,
buffered datum and raw descending-copy solution. Whole-window charts are
replaced by the real Eulerian coefficient hypotheses and its Schur budget;
local-to-global sampling supplies those hypotheses. The fixed-point/restart
and the expansion consumers are already proved. The degenerate cases are included: H=0 has no
defect; empty and singleton types, D=2, constants, zero data, identity geometry, an
edgeless seed and a point post-buffer window retain precisely these maps.
No independent solution or mass-dependent map is chosen. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace preparationNeutralEnergyAdd preparationNeutralEnergyMonoid
  preparationNeutralEnergyModule
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}


/-- The exact physical finite-route insertion price, with both raw-path
ingredients discharged from the same supplied solution and coefficients. -/
theorem actual_finite_route_join
    (family : ChartedFamily ι h D Part Ctx) (H Kbase Kmax : ℕ)
    (ν ρ a c b e Esc : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (π : ι → ℝ) (_hπ : ∀ i, 0 < π i)
    (actual : ∀ p, Ctx p)
    (_Kbound : ∀ x : ι × Fin (H + 1), preparationNeutralSlots H D Kbase x ≤ Kmax)
    (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (u : (∀ i, TorusHk 0 (h i)) →
      ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1))
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) =
      (M.full f).1 ⟨c, hac, hcb⟩ i)
    (_hhom : ScalarFamilyEnergyPathRealizes (ν := ν) hcb
      v
      (fun i (f : ∀ j, TorusHk 0 (h j)) => (f i, 0)) M.homogeneous)
    (_hreal : ∀ f, ∃ W : ∀ x : ι × Fin (H + 1), ℝ →
        TorusHk (preparationNeutralSlots H D Kbase x + 1) (h x.1),
      IsCoupledWeakSolutionTorus ν c b v D (preparationNeutralSlots H D Kbase)
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))
        (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) (B f))
        (fun _ _ => 0) (fun _ _ => 0) (u f) W ∧
      (∀ l, ∀ t : Set.Icc c b, (E l f).1 t = fun i =>
        truncateTorusHk (Nat.zero_le _) (u f (i, l) t)) ∧
      (∀ l, (E l f).2 =ᵐ[volume.restrict (Set.Icc c b)] fun t =>
        coupledCarrierHighJets (fun _ => 0) (fun i =>
          truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l) t))))
    (Pq : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) c b ρ ν 0 D)
    (P : PreparationPlainKernelFrame Pq)
    (_hcoeff : ∀ i j γ d, Pq.B i j γ d =
      constituentPhysical family ν e Esc actual i j γ d.val)
    (_hincl : ∀ i j γ, Pq.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (_hsource : ScalarFamilyEnergyPathRealizes (ν := ν) Pq.htime
      v (preparationKernelScalarDatum Pq) M.source)
    (_hD : 2 ≤ D)
    (_hd : TorusDriftData ν ρ c b
      v Kmax)
    (_hreserve : ∀ (l : Fin H) j, P.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (q S Sr Cbuf : ℝ) (_hq : 0 ≤ q) (_hSr : 0 ≤ Sr)
    (_hw : ∀ i j γ, (P.spec i j γ).width ≤ q * ρ)
    (_hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * P.rows.basePrice i j))
    (_hraw_schur : SchurBound Sr
      (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
        (preparationNeutralSlots H D Kbase) D c b
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))))
    (_hfinite : ∀ x y d, coefficientSeminorm ρ
      (preparationNeutralSlots H D Kbase x) c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d) ≠ ⊤)
    (_hmeas : ∀ x y d, Measurable (fun p : Set.Icc c b × Vec 2 =>
      edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d p.1 p.2))
    (_hsmooth : ∀ x y d t, t ∈ Set.Icc c b → ContDiff ℝ
      (preparationNeutralSlots H D Kbase x : ℕ)
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hper : ∀ x y d t, t ∈ Set.Icc c b → IsZ2Periodic
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hbuf : ∀ f, Real.sqrt (massNormSq ρ π (fun i => (B f i).val)) ≤
      Cbuf * Real.sqrt (massNormSq ρ π (fun i => (f i).val))) :
    ActualFiniteRouteJoinStatement family H Kbase Kmax ν ρ a c b e Esc v π _hπ actual _Kbound hac hcb M B u E _hB _hhom _hreal Pq P _hcoeff _hincl _hsource _hD _hd _hreserve q S Sr Cbuf _hq _hSr _hw _hs _hraw_schur _hfinite _hmeas _hsmooth _hper _hbuf := by
  apply actual_finite_route_of_ingredients family H Kbase Kmax ν ρ a c b e Esc v π _hπ actual _Kbound hac hcb M B u E _hB _hhom _hreal Pq P _hcoeff _hincl _hsource _hD _hd _hreserve q S Sr Cbuf _hq _hSr _hw _hs _hraw_schur _hfinite _hmeas _hsmooth _hper _hbuf
  · exact raw_buffered_copy_join family H Kbase Kmax ν ρ a c b e Esc v actual hac hcb M B u E _hB _hhom _hreal _hd Pq.diffusivity_pos Pq.radius_pos
  · exact raw_post_buffer_price family H Kbase Kmax ν ρ c b e Esc v π _hπ actual _Kbound B u E _hreal Pq P _hcoeff _hincl M.source _hsource _hD _hd _hreserve q S Sr _hq _hSr _hw _hs _hraw_schur _hfinite _hmeas _hsmooth _hper
end

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Sampled source and raw rank budgets price the same supplied native route. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace preparationNeutralEnergyAdd preparationNeutralEnergyMonoid
  preparationNeutralEnergyModule
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

/-- The exact native plain-defect row, with sampled price and moment decay discharged. -/
theorem nativeDefectRow
    (family : ChartedFamily ι h D Part Ctx) (H Kbase Kmax : ℕ)
    (ν ρ a c b e Esc : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (π : ι → ℝ) (_hπ : ∀ i, 0 < π i)
    (actual : ∀ p, Ctx p)
    (_Kbound : ∀ x : ι × Fin (H + 1), preparationNeutralSlots H D Kbase x ≤ Kmax)
    (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (u : (∀ i, TorusHk 0 (h i)) →
      ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1))
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) =
      (M.full f).1 ⟨c, hac, hcb⟩ i)
    (_hhom : ScalarFamilyEnergyPathRealizes (ν := ν) hcb
      v
      (fun i (f : ∀ j, TorusHk 0 (h j)) => (f i, 0)) M.homogeneous)
    (_hreal : ∀ f, ∃ W : ∀ x : ι × Fin (H + 1), ℝ →
        TorusHk (preparationNeutralSlots H D Kbase x + 1) (h x.1),
      IsCoupledWeakSolutionTorus ν c b v D (preparationNeutralSlots H D Kbase)
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))
        (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) (B f))
        (fun _ _ => 0) (fun _ _ => 0) (u f) W ∧
      (∀ l, ∀ t : Set.Icc c b, (E l f).1 t = fun i =>
        truncateTorusHk (Nat.zero_le _) (u f (i, l) t)) ∧
      (∀ l, (E l f).2 =ᵐ[volume.restrict (Set.Icc c b)] fun t =>
        coupledCarrierHighJets (fun _ => 0) (fun i =>
          truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l) t))))
    (Pq : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) c b ρ ν 0 D)
    (P : PreparationPlainKernelFrame Pq)
    (_hcoeff : ∀ i j γ d, Pq.B i j γ d =
      constituentPhysical family ν e Esc actual i j γ d.val)
    (_hincl : ∀ i j γ, Pq.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (_hsource : ScalarFamilyEnergyPathRealizes (ν := ν) Pq.htime
      v (preparationKernelScalarDatum Pq) M.source)
    (_hD : 2 ≤ D)
    (_hd : TorusDriftData ν ρ c b
      v Kmax)
    (_hreserve : ∀ (l : Fin H) j, P.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (q Sr Cbuf : ℝ) (_hq : 0 ≤ q) (_hSr : 0 ≤ Sr)
    (_hw : ∀ i j γ, (P.spec i j γ).width ≤ q * ρ)
    (_hraw_schur : SchurBound Sr
      (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
        (preparationNeutralSlots H D Kbase) D c b
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))))
    (_hfinite : ∀ x y d, coefficientSeminorm ρ
      (preparationNeutralSlots H D Kbase x) c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d) ≠ ⊤)
    (_hmeas : ∀ x y d, Measurable (fun p : Set.Icc c b × Vec 2 =>
      edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d p.1 p.2))
    (_hsmooth : ∀ x y d t, t ∈ Set.Icc c b → ContDiff ℝ
      (preparationNeutralSlots H D Kbase x : ℕ)
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hper : ∀ x y d t, t ∈ Set.Icc c b → IsZ2Periodic
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hbuf : ∀ f, Real.sqrt (massNormSq ρ π (fun i => (B f i).val)) ≤
      Cbuf * Real.sqrt (massNormSq ρ π (fun i => (f i).val)))
    (Ks : ι → ℕ) (Cs : ℝ) (_hCs : 0 ≤ Cs) (Bm : ι → ι → ℝ) (_hBm : ∀ i j, 0 ≤ Bm i j)
    (_hsampled : IsSampledEnvelope family π Ks actual c b ν e Esc ρ Cs Bm)
    (Sinc : ℝ) (_hSinc0 : 0 ≤ Sinc) (_hSinc : SchurBound Sinc Bm)
    (Fm : PreparationMomentBudgetParameters) (m : ℕ) (_hm : 1 ≤ m)
    (_hFL : P.L = Fm.L) (_hFH : H = Fm.H) (_hFbuf : Cbuf = Fm.Cbuf)
    (_hFsample : preparationPlainSampledConstant P.φ P.matrix_bound D P.L * Cs ≤ Fm.Csample)
    (_hwidth : q ≤ Fm.Cwid * ocEpsilon Fm.q Fm.Λ m ^ Fm.σ)
    (_hinc : Sinc ≤ Fm.CI * ocEpsilon Fm.q Fm.Λ m ^ Fm.θ)
    (_hraw : Sr ≤ Fm.Cplain * Sinc) :
  ∀ (f : ∀ i, TorusHk 0 (h i)) (l : ℕ), l < H →
    preparationWeightedPathEnergy (h := h) ρ π ν a b c
      (preparationBufferedPlainLayer hac hcb M E (l + 1) f -
        preparationBufferedKernelMap hcb M.source
          (preparationBufferedPlainLayer hac hcb M E l f)) ≤
      preparationMomentDefectConstant Fm * ocEpsilon Fm.q Fm.Λ (m - 1) ^ (Fm.q * Fm.σ * Fm.L) *
        Real.sqrt (massNormSq ρ π (fun i => (f i).val))
 := by
  classical
  let cs := preparationPlainSampledConstant P.φ P.matrix_bound D P.L
  let S := (ν * cs * Cs) * Sinc
  have hcs : 0 ≤ cs := preparation_plain_sampled_constant_nonneg _ _ _ _
  have hS : 0 ≤ S := mul_nonneg
    (mul_nonneg (mul_nonneg Pq.diffusivity_pos.le hcs) _hCs) _hSinc0
  have hC : ∀ i j γ, ‖Pq.C i j γ‖ ≤ 1 := by
    intro i j γ
    rw [_hincl i j γ]
    exact ContinuousLinearMap.norm_id_le
  have hprice := P.price_of_sampled π _hπ Ks e Esc actual _hcoeff hC
    Cs _hCs Bm _hBm _hsampled
  have hschur := P.schur_of_sampled_price π Cs _hCs Bm Sinc hprice _hSinc
  let X : PreparationMomentBudgetData Fm m := {
    width := q
    ν := ν
    source := S
    incidence := Sinc
    width_nonneg := _hq
    diffusivity_pos := Pq.diffusivity_pos
    incidence_nonneg := _hSinc0
    width_le := _hwidth
    incidence_le := _hinc
    source_le := by
      rw [abs_of_nonneg hS]
      calc
        S = ν * (cs * Cs) * Sinc := by dsimp [S]; ring
        _ ≤ ν * Fm.Csample * Sinc := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left _hFsample Pq.diffusivity_pos.le) _hSinc0 }
  have hrank : (8 * Sr + 1) ^ Fm.H ≤ (8 * (Fm.Cplain * Sinc) + 1) ^ Fm.H :=
    pow_le_pow_left₀
      (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) _hSr)
        (by norm_num : (0 : ℝ) ≤ 1))
      (add_le_add
        (mul_le_mul_of_nonneg_left _hraw (by norm_num : (0 : ℝ) ≤ 8)) le_rfl) Fm.H
  have hpre : 0 ≤ 14 * (q ^ Fm.L * |S| / ν) := mul_nonneg (by norm_num)
    (div_nonneg (mul_nonneg (pow_nonneg _hq _) (abs_nonneg S)) Pq.diffusivity_pos.le)
  have hcoef : 14 * (q ^ P.L * |S| / ν) * (8 * Sr + 1) ^ H * Cbuf ≤
      preparationMomentDefectPrice Fm X := by
    change _ ≤ 14 * (q ^ Fm.L * |S| / ν) * (8 * (Fm.Cplain * Sinc) + 1) ^ Fm.H * Fm.Cbuf
    rw [_hFL, _hFH, _hFbuf]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrank hpre)
      Fm.buffer_nonneg
  have hpower := uniform_moment_defect_power Fm m _hm X
  have hfinite := actual_finite_route_join family H Kbase Kmax ν ρ a c b e Esc v
    π _hπ actual _Kbound hac hcb M B u E _hB _hhom _hreal Pq P _hcoeff _hincl
    _hsource _hD _hd _hreserve q S Sr Cbuf _hq _hSr _hw hschur
    _hraw_schur _hfinite _hmeas _hsmooth _hper _hbuf
  intro f l hl
  exact (hfinite f l hl).trans (mul_le_mul_of_nonneg_right (hcoef.trans hpower)
    (Real.sqrt_nonneg _))
end

/-! **The native route core** (the route part of the actual preparation context), over an abstract family (ι, h), at a native operator `P` on `[a, b]`, its buffered
maps `M` (realized, buffer end `c`) and a buffered datum `B` in the copy-zero slot.

* `CopyClauses`: the coefficient clauses of the copied chain on `[c, b]` (finite seminorms,
  measurability, smoothness, periodicity).
* `route_copies`: ONE raw copied solution `L` with energy paths `E` of the neutral chain of
  `family` (`rawCopiedEnergyPaths`), whose layers `(E l) ∘ B` give the buffered plain-layer
  join of `M` (`raw_buffered_copy_join`).
* `massNormSq_order_zero_radius`: the order-zero mass norm does not depend on the radius.
* `route_defect`: the priced defect row at one weight (`nativeDefectRow`).
* `NativeFacts`, `NativeExists`, `native_frame_copies`: the native objects `M, B, L, E`
  with their facts, from a native buffer input (`native_preparation_frame_join`) and the copy
  clauses.
* `native_rows` (the three supplied energy rows), `gate_buffer` (the buffer bound in the
  form used by the joint preparation), `copy_solve` (the copied solution with its plain readout).

For `H = 0` there is no defect; an empty index type `ι` and the zero datum are allowed. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace preparationNeutralEnergyAdd preparationNeutralEnergyMonoid
  preparationNeutralEnergyModule
attribute [local instance] preparationNeutralSlotsMonoid preparationNeutralSlotsModule

variable {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

/-- The buffered datum at the copy-zero slot order (the same map; the slot of copy zero is the
buffer order `K_base + H (D − 2)`). -/
def SlotCast {H D Kbase : ℕ}
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i))) :
    (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, (0 : Fin (H + 1)))) (h i)) := B

/-- The coefficient clauses of the copied chain on the window `[c, b]`. -/
def CopyClauses (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) (ν ρ c b e Esc : ℝ)
    (actual : ∀ p, Ctx p) : Prop :=
  (∀ x y d, coefficientSeminorm ρ (preparationNeutralSlots H D Kbase x) c b
    (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
      (preparationNeutralSlots H D Kbase) x y d) ≠ ⊤) ∧
  (∀ x y d, Measurable (fun p : Set.Icc c b × Vec 2 =>
    edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
      (preparationNeutralSlots H D Kbase) x y d p.1 p.2)) ∧
  (∀ x y d t, t ∈ Set.Icc c b → ContDiff ℝ (preparationNeutralSlots H D Kbase x : ℕ)
    (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
      (preparationNeutralSlots H D Kbase) x y d t)) ∧
  ∀ x y d t, t ∈ Set.Icc c b → IsZ2Periodic
    (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
      (preparationNeutralSlots H D Kbase) x y d t)

/-- **The copied solution and the buffered join.** -/
theorem route_copies (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) (hD : 2 ≤ D)
    (ν ρ a c b e Esc : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (φ : ℝ → Vec 2 → ℝ)
    (actual : ∀ p, Ctx p) (hac : a ≤ c) (hcb : c ≤ b)
    (hd : TorusDriftData ν ρ c b (streamVel φ) (Kbase + H * (D - 2)))
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) = (M.full f).1 ⟨c, hac, hcb⟩ i)
    (hcl : CopyClauses family H Kbase ν ρ c b e Esc actual) :
    ∃ (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
        (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
      (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) H c b),
      RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc (streamVel φ)
        actual (SlotCast B) (fun f => L (SlotCast B f)) E ∧
      BufferedPlainLayerJoinStatement hac hcb M E := by
  obtain ⟨hfin, hmeas, hsmooth, hper⟩ := hcl
  have hK : ∀ x : ι × Fin (H + 1), preparationNeutralSlots H D Kbase x ≤ Kbase + H * (D - 2) :=
    fun x => Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _
  have hzero : ∀ x y d, x.2.val ≠ y.2.val + 1 → ∀ t ∈ Set.Icc c b,
      edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t = 0 := by
    intro x y d hxy t _
    rw [raw_neutral_edge_zero family H ν e Esc actual _ x y d hxy]
    rfl
  have hRaw := rawCopiedEnergyPaths (ι := ι) (h := h) H D (Kbase + H * (D - 2))
    (preparationNeutralSlots H D Kbase) hD hK ν ρ c b (streamVel φ) hν hρ hcb hd
    (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
      (preparationNeutralSlots H D Kbase)) hfin hmeas hsmooth hper hzero
  obtain ⟨L, hRaw⟩ := hRaw
  obtain ⟨E, hLE⟩ := hRaw
  have hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc
      (streamVel φ) actual (SlotCast B) (fun f => L (SlotCast B f))
        (fun l => (E l).comp (SlotCast B)) := fun f => hLE (SlotCast B f)
  have hJ := raw_buffered_copy_join family H Kbase (Kbase + H * (D - 2)) ν ρ a c b
    e Esc (streamVel φ) actual hac hcb M (SlotCast B) (fun f => L (SlotCast B f))
    (fun l => (E l).comp (SlotCast B)) hB hM.2.1 hreal hd hν hρ
  exact ⟨L, fun l => (E l).comp (SlotCast B), hreal, hJ.1⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The order-zero mass norm does not depend on the radius. -/
theorem massNormSq_order_zero_radius [Fintype ι] (ρ : ℝ) (π : ι → ℝ)
    (f : ∀ i, TorusHk 0 (h i)) :
    massNormSq ρ π (fun i => (f i).val) = massNormSq 1 π (fun i => (f i).val) := by
  rw [CycleJointProofs.massNormSq_order_zero, CycleJointProofs.massNormSq_order_zero]

omit [DecidableEq ι] in
/-- **The priced defect row of the route at one weight**, from defect row, with the
order-zero norms at radius one. -/
theorem route_defect (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) (hD : 2 ≤ D)
    (ν ρ a c b e Esc : ℝ) (φ : ℝ → Vec 2 → ℝ) (actual : ∀ p, Ctx p) (hac : a ≤ c) (hcb : c ≤ b)
    (hd : TorusDriftData ν ρ c b (streamVel φ) (Kbase + H * (D - 2)))
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) = (M.full f).1 ⟨c, hac, hcb⟩ i)
    (hcl : CopyClauses family H Kbase ν ρ c b e Esc actual)
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b)
    (hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc
      (streamVel φ) actual (SlotCast B) (fun f => L (SlotCast B f)) E)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (Cbuf : ℝ)
    (hbound : ∀ f, Real.sqrt (massNormSq ρ π (fun i => (B f i).val)) ≤
      Cbuf * Real.sqrt (massNormSq 1 π (fun i => (f i).val)))
    (Sr : ℝ) (hSr : 0 ≤ Sr)
    (hschur : SchurBound Sr (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
      (preparationNeutralSlots H D Kbase) D c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase))))
    (PF : PreparationPlainKernelFrame
      (Buffer.kernelOperator_time_restrict P (Set.Icc_subset_Icc hac le_rfl) hcb))
    (hcoeff : ∀ i j γ d, (Buffer.kernelOperator_time_restrict P
      (Set.Icc_subset_Icc hac le_rfl) hcb).B i j γ d =
        constituentPhysical family ν e Esc actual i j γ d.val)
    (hincl : ∀ i j γ, (Buffer.kernelOperator_time_restrict P
      (Set.Icc_subset_Icc hac le_rfl) hcb).C i j γ = ContinuousLinearMap.id ℝ (h j))
    (hreserve : ∀ (l : Fin H) j, PF.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (qw : ℝ) (hqw : 0 ≤ qw) (hw : ∀ i j γ, (PF.spec i j γ).width ≤ qw * ρ)
    (Ks : ι → ℕ) (Cs : ℝ) (hCs : 0 ≤ Cs) (Bm : ι → ι → ℝ) (hBm : ∀ i j, 0 ≤ Bm i j)
    (hsampled : IsSampledEnvelope family π Ks actual c b ν e Esc ρ Cs Bm)
    (Sinc : ℝ) (hSinc0 : 0 ≤ Sinc) (hSinc : SchurBound Sinc Bm)
    (Fm : PreparationMomentBudgetParameters) (m : ℕ) (hm : 1 ≤ m) (hFL : PF.L = Fm.L)
    (hFH : H = Fm.H) (hFbuf : Cbuf = Fm.Cbuf)
    (hFsample : preparationPlainSampledConstant PF.φ PF.matrix_bound D PF.L * Cs ≤ Fm.Csample)
    (hwidth : qw ≤ Fm.Cwid * ocEpsilon Fm.q Fm.Λ m ^ Fm.σ)
    (hinc : Sinc ≤ Fm.CI * ocEpsilon Fm.q Fm.Λ m ^ Fm.θ) (hraw : Sr ≤ Fm.Cplain * Sinc) :
    ∀ (f : ∀ i, TorusHk 0 (h i)) (l : ℕ), l < H →
      preparationWeightedPathEnergy (h := h) ρ π ν a b c
        (preparationBufferedPlainLayer hac hcb M E (l + 1) f -
          preparationBufferedKernelMap hcb M.source
            (preparationBufferedPlainLayer hac hcb M E l f)) ≤
        preparationMomentDefectConstant Fm * ocEpsilon Fm.q Fm.Λ (m - 1) ^ (Fm.q * Fm.σ * Fm.L) *
          Real.sqrt (massNormSq 1 π (fun i => (f i).val)) := by
  have hK : ∀ x : ι × Fin (H + 1), preparationNeutralSlots H D Kbase x ≤ Kbase + H * (D - 2) :=
    fun x => Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _
  obtain ⟨hfin, hmeas, hsmooth, hper⟩ := hcl
  have hbufρ : ∀ f, Real.sqrt (massNormSq ρ π (fun i => (SlotCast B f i).val)) ≤
      Cbuf * Real.sqrt (massNormSq ρ π (fun i => (f i).val)) := by
    intro f
    rw [massNormSq_order_zero_radius ρ π f]
    exact hbound f
  intro f l hl
  have hrow := nativeDefectRow family H Kbase (Kbase + H * (D - 2)) ν ρ a c b e Esc
    (streamVel φ) π hπ actual hK hac hcb M (SlotCast B) (fun f => L (SlotCast B f))
    E hB hM.2.1 hreal _ PF hcoeff hincl hM.2.2 hD hd
    hreserve qw Sr Cbuf hqw hSr hw hschur hfin hmeas hsmooth hper hbufρ Ks Cs hCs Bm hBm
    hsampled Sinc hSinc0 hSinc Fm m hm hFL hFH hFbuf hFsample hwidth hinc hraw f l hl
  refine le_trans (le_of_eq ?_) (hrow.trans (le_of_eq ?_))
  · rfl
  · rw [massNormSq_order_zero_radius ρ π f]

omit [DecidableEq ι] in
/-- The native weak equation of the full map of realized buffered maps, on the whole window. -/
theorem native_of_realizes {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j γ, NormedAddCommGroup (G i j γ)]
    [∀ i j γ, InnerProductSpace ℝ (G i j γ)] [∀ i j γ, FiniteDimensional ℝ (G i j γ)]
    [∀ i j γ, MeasurableSpace (G i j γ)] [∀ i j γ, BorelSpace (G i j γ)]
    [∀ i j γ, CompleteSpace (G i j γ)] {a b c ρ ν : ℝ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) :
    ∀ f, ∃ (w : ∀ i, ℝ → TorusHk 1 (h i))
      (y : ∀ i j (γ : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j γ)),
      IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D P.B P.C P.S f (fun _ _ => 0)
        (fun _ _ => 0) (fun i t => (M.full f).1 (Set.projIcc a b (hac.trans hcb) t) i) w y := by
  intro f
  obtain ⟨w, y, hs, -⟩ := hM.1 f
  exact ⟨w, y, hs⟩

/-- The facts of the native objects: the realized buffered maps `M` with their fixed point, the
buffered datum `B` with its trace, buffer bound and constant trace, the raw copied solution `L` and
the post-buffer plain maps `E` with the buffered join. -/
def NativeFacts (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) {a b c ρ ν : ℝ}
    (e Esc : ℝ) (actual : ∀ p, Ctx p)
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (π : ι → ℝ) (weights : Set (ι → ℝ)) (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b) : Prop :=
  BufferedKernelMapsRealizes P φ hac hcb M ∧ M.IsFixedPoint hac hcb ∧
  (∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) = (M.full f).1 ⟨c, hac, hcb⟩ i) ∧
  (∀ r : ℝ, 0 ≤ r → r ≤ ρ → ∀ w ∈ weights, ∀ f,
    Real.sqrt (massNormSq r (fun i => π i / w i ^ 2) (fun i => (B f i).val)) ≤
      Real.sqrt (Buffer.bufferEnergyCost (Kbase + H * (D - 2))) *
        Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (f i).val))) ∧
  BufferedConstantTraceStatement (fun _ => Kbase + H * (D - 2)) B ∧
  RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc
    (streamVel φ) actual (SlotCast B) (fun f => L (SlotCast B f)) E ∧
  BufferedPlainLayerJoinStatement hac hcb M E

/-- The native objects exist with their facts. -/
def NativeExists (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) {a b c ρ ν : ℝ}
    (e Esc : ℝ) (actual : ∀ p, Ctx p)
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (π : ι → ℝ) (weights : Set (ι → ℝ)) (hcb : c ≤ b) : Prop :=
  ∃ (hac : a ≤ c)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (Kbase + H * (D - 2)) (h i)))
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b),
    NativeFacts family H Kbase e Esc actual P φ π weights hac hcb M B L E

/-- **The native frame and copies over an abstract family**: the native frame of a buffer input
(`native_preparation_frame_join`), the copied solution and the buffered join
(`route_copies`). -/
theorem native_frame_copies (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ)
    (hD : 2 ≤ D) {a b c ρ ν : ℝ} (hc : c = a + ρ ^ 2 / ν) (hν : 0 < ν) (hρ : 0 < ρ)
    (e Esc : ℝ) (actual : ∀ p, Ctx p)
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (OC : OCData) (m : ℕ) (π : ι → ℝ) (weights : Set (ι → ℝ))
    (I : PreparationNativeBufferInput (c := c) P OC m (Kbase + H * (D - 2)) π weights)
    (hcb : c ≤ b)
    (hd : TorusDriftData ν ρ c b (streamVel (OC.Φ m)) (Kbase + H * (D - 2)))
    (hcl : CopyClauses family H Kbase ν ρ c b e Esc actual) :
    NativeExists family H Kbase e Esc actual P (OC.Φ m) π weights hcb := by
  subst hc
  have hJ := native_preparation_frame_join P OC m (Kbase + H * (D - 2)) π weights I hd
  obtain ⟨hac, hJ⟩ := hJ
  obtain ⟨M, hJ⟩ := hJ
  obtain ⟨-, hreal, hfix, hJ⟩ := hJ
  obtain ⟨B, hB, hbound, hconst⟩ := hJ
  have hX := route_copies family H Kbase hD ν ρ a (a + ρ ^ 2 / ν) b e Esc hν hρ (OC.Φ m)
    actual hac hcb hd P M hreal B hB hcl
  obtain ⟨L, hX⟩ := hX
  obtain ⟨E, hX⟩ := hX
  obtain ⟨hrealC, hjoin⟩ := hX
  exact ⟨hac, M, B, L, E, hreal, hfix, hB, hbound, hconst, hrealC, hjoin⟩

/-- **The three supplied energy rows of the native route at every weight**
(`supplied_native_weighted_energy`). -/
theorem native_rows (family : ChartedFamily ι h D Part Ctx) (Kbuf : ℕ)
    {a b c ρ ν : ℝ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ) (G := fun _ j _ => h j)
      a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (π : ι → ℝ) (weights : Set (ι → ℝ))
    (operators : ∀ w ∈ weights, KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) a b ρ ν 0 D)
    (hagree : ∀ w hw, PreparationKernelDataAgreement P (operators w hw))
    (hmass : ∀ w hw, (operators w hw).π = fun i => π i / w i ^ 2)
    (hφ : IsAdmissibleStream φ) (hac : a ≤ c) (hcb : c ≤ b)
    (hd : TorusDriftData ν ρ c b (streamVel φ) Kbuf) (Θ : ℝ)
    (htheta : ∀ w hw, (operators w hw).θ = Θ)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hM : BufferedKernelMapsRealizes P φ hac hcb M) (w : ι → ℝ) (hw : w ∈ weights) :
    (∀ f, preparationWeightedPathEnergy (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
      (M.full f) ≤ 2 * Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2)
        (fun i => (f i).val))) ∧
    (∀ x, preparationWeightedPathEnergy (h := h) ρ (fun i => π i / w i ^ 2) ν a b c
      (preparationBufferedKernelMap hcb M.source x) ≤
        7 * |Θ| * preparationWeightedPathEnergy (h := h) ρ (fun i => π i / w i ^ 2) ν a b c x) ∧
    ∀ (x : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) (t : Set.Icc a b),
      Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (x.1 t i).val)) ≤
        preparationWeightedPathEnergy (h := h) ρ (fun i => π i / w i ^ 2) ν a b c x :=
  supplied_native_weighted_energy P φ hφ hac hcb hd π weights operators Θ hagree hmass
    htheta M hM w hw

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The buffer bound in the form used by the joint preparation (sum of `torusHkNorm` squares). -/
theorem gate_buffer {K0 : ℕ} (π : ι → ℝ) (r C : ℝ)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk K0 (h i)))
    (hB : ∀ f, Real.sqrt (massNormSq r π (fun i => (B f i).val)) ≤
      C * Real.sqrt (massNormSq 1 π (fun i => (f i).val))) (f : ∀ i, TorusHk 0 (h i)) :
    Real.sqrt (∑ i, (π i)⁻¹ * torusHkNorm r (le_refl K0) (B f i) ^ 2) ≤
      C * Real.sqrt (massNormSq 1 π (fun i => (f i).val)) := by
  have he : (∑ i, (π i)⁻¹ * torusHkNorm r (le_refl K0) (B f i) ^ 2) =
      massNormSq r π (fun i => (B f i).val) := by
    unfold massNormSq torusHkNorm
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.sq_sqrt (factorialNormSq_nonneg _ _)]
    rfl
  rw [he]
  exact hB f

omit [DecidableEq ι] in
/-- The copied solution of a raw copy realization, with its plain readout. -/
theorem copy_solve (family : ChartedFamily ι h D Part Ctx) (H Kbase : ℕ) {ν c b e Esc : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {actual : ∀ p, Ctx p}
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (L : (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1)))
    (E : PreparationPostPlainMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) H c b)
    (hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase) ν c b e Esc v
      actual B (fun f => L (B f)) E) (f : ∀ i, TorusHk 0 (h i)) :
    ∃ (u : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x) (h x.1))
      (w : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase x + 1) (h x.1)),
      IsCoupledWeakSolutionTorus ν c b v D (preparationNeutralSlots H D Kbase)
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))
        (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) (B f))
        (fun _ _ => 0) (fun _ _ => 0) u w ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc c b),
        (∑ l : Fin (H + 1), (E l f).1 ⟨t, ht⟩) =
          CopyJoint.plainReadout (preparationNeutralSlots H D Kbase) u t := by
  have hr := hreal f
  obtain ⟨W, hr⟩ := hr
  refine ⟨L (B f), W, hr.1, fun t ht => ?_⟩
  funext i
  rw [Finset.sum_apply]
  unfold CopyJoint.plainReadout
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hr.2.1 l ⟨t, ht⟩]
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Uniform assembly of the exact common-preparation production statement.
The four fixed-stage ingredients share one operator route and one model, and
all constants and the insertion depth precede the data. The statement assumes
that these routes can be realized uniformly.

Empty and singleton families, an edgeless seed and p=0 retain the scalar endpoint.
Hpr is selected before the seed constants, so the reserve floor cannot
depend on G0 or Hprod. The model precedes both the datum and the weight. -/

open AVRegularity.Construction.Preservation.Assembly FullLift CycleComparison.Coarse

/-- A common route and endpoint with its separately named analytic ingredients.
This is a joint witness type; its uniform production
must establish the four displayed statements for the same route and model. -/
structure PreparationRouteWitness {hr : ℕ → Type}
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (F : Request hr D Dm bw j₀) (Cexp Cjoint Cjet : ℝ) where
  X : Type
  [group : AddCommGroup X]
  [moduleSpace : Module ℝ X]
  route : F.InsertionRoute X
  model : F.Model
  jet_constant_nonneg : 0 ≤ Cjet
  covariance_order : F.Naux + 2 * F.p ≤ F.Nout
  radius_positive : 0 < rhoEnh D F.cr F.G.level
  covariance_small : fbCovConst (rhoEnh D F.cr F.G.level)
    (covPrimitive D F.G.level model.tp) F.Nout ≤ 1
  operators : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    RetainedEnergy.NativeEnergyOperatorAt F.P F.seedK F.freshK F.φ₀ F.hφ₀ F.G F.s F.tf
      (rhoStar D F.c₀ F.G.level) (D.κ F.G.level) 0 (fun v => F.G.mass F.law v / w v ^ 2)
  actual_evolution : F.RealizedEvolutionStatement route
  expansion : F.FiniteExpansionApproximationStatement route model Cexp
  neutral_model : F.NeutralChainModelStatement route model Cjoint Cjet
  endpoint : F.EndpointStatement model

/-- Data binders, verbatim from CommonPreparationProductionDataStatement, with
one shared route in place of the already assembled preparation. -/
def CommonPreparationRouteDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (Hpr : ℕ) (Cexp Cjoint Cjet Q T₀ : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    Nonempty (PreparationRouteWitness
      ({ law := law, P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p,
         seedK := seedK, freshK := freshK, φ₀ := φ₀, hφ₀ := hφ₀, G := G,
         cr := kI.cr, c₀ := kI.c₀, Q := Q, s := s₀, tf := tf, p := p,
         Nout := Nout, Naux := Naux, Hpr := Hpr } : Request hr D _ bw j₀)
      Cexp Cjoint Cjet)

/-- Uniform choices for the four named route ingredients, before every datum. -/
def UniformCommonPreparationRouteStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∃ Hpr Kneed : ℕ, ∀ sX sZ : ℕ,
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (Cexp Cjoint Cjet : ℝ) (mStar : ℕ),
    CommonPreparationRouteDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ Hpr Cexp Cjoint Cjet Q T₀ mStar

/-- The literal uniform production statement follows from the uniform route
with no change of the choice order or the endpoint outputs. -/
theorem common_preparation_production_of_routes (α s q : ℝ) (ζ : ℝ → ℝ)
    (hroute : UniformCommonPreparationRouteStatement α s q ζ) :
    CommonPreparationProductionStatement α s q ζ := by
  obtain ⟨Λ₀, hΛ₀, hroute⟩ := hroute
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, hroute⟩ := hroute Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hsmooth hnonneg hmass hsupp bw hbw hbwsmall Q T₀ hQ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
    σ₀ a σ hsched haux hout
  obtain ⟨Hpr, Kneed, hroute⟩ := hroute φ₀ hφ₀ hsmooth hnonneg hmass hsupp bw hbw hbwsmall
    Q T₀ hQ hT₀ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad σ₀ a σ hsched haux hout
  refine ⟨Kneed, ?_⟩
  intro sX sZ hsX hsZ Ce kS hCe hc₀ hc₀max hcr hcr1 hσf hlamC halloc hKs hKan hLan hJm
  obtain ⟨thr, CH, Υ, hCH, hΥ, hroute⟩ := hroute sX sZ hsX hsZ Ce kS hCe hc₀ hc₀max hcr hcr1
    hσf hlamC halloc hKs hKan hLan hJm
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hroute⟩ := hroute kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨Cexp, Cjoint, Cjet, mStar, hroute⟩ := hroute CI Cw j₀ hledger hstart
  refine ⟨((p : ℝ) + 1) * Cjet, max (Cjoint + Cexp) Cjet, mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hstream M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed hpointwise
    m hm hmn hn tA s₀ htS htA htf hlength G G' hcascade hlevel hinv hsucc
  obtain ⟨W⟩ := hroute D hDα hDq hDΛ hDζ hstream M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed hpointwise m hm hmn hn tA s₀ htS htA htf hlength
    G G' hcascade hlevel hinv hsucc
  let _ := W.group
  let _ := W.moduleSpace
  have hφ : IsAdmissibleStream (D.Φ G.level) := by
    simpa only [Nat.add_sub_cancel] using
      (hstream.2 (G.level + 1) (Nat.succ_pos G.level)).choose
  have ht : W.model.tp ∈ Set.Icc s₀ tf := by
    have hb := W.endpoint.2.1
    have hp := W.endpoint.2.2.1
    have hs := W.endpoint.1
    have htf' : s₀ + 4 * ocTauPP D.α D.q D.Λ G.level ≤ tf := by
      simpa only [hlevel, hDα, hDq, hDΛ] using htf
    exact ⟨hs.trans hp.1, by linarith only [hb, hp.2, htf']⟩
  have hmasses : ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
      ∀ v, 0 < G.mass law v / w v ^ 2 := by
    intro w hw
    obtain ⟨Rw, _, _, _, hπ⟩ := W.operators w hw
    simpa only [hπ] using Rw.hπ
  have hevol := evolution_trace_of_native_operators _ W.route W.model _
    W.operators hφ ht W.actual_evolution
  have hp := common_preparation_of_insertion_route _ W.route W.model Cexp Cjoint Cjet
    hmasses W.jet_constant_nonneg W.covariance_order W.radius_positive
    W.covariance_small hevol W.expansion W.neutral_model W.endpoint
  refine ⟨W.model.tp, W.model.map, hp.1, ?_, ?_⟩
  · simpa only [Request.bufferEnd, hlevel] using hp.2.1
  · simpa only [hlevel, hDα, hDq, hDΛ, hDζ] using hp.2.2

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
