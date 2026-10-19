-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.KernelEnergyBounds
public import AVRegularity.Construction.Preservation.CommonPreparation.NativeOperatorTower
import AVRegularity.CycleJoint.PeriodicOperatorLocalization

section
section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Glue the actual finite plain chain into the physical buffered path space.
Copy zero retains the native pre-buffer trace; positive copies extend by zero.
The higher classes are unchanged and every positive defect is the extension
of the SAME post-buffer plain-minus-kernel response.

The degenerate cases are included: depth zero gives only the homogeneous restart. Empty and
singleton families, zero/constants, D=2, identity geometry, edgeless seeds and a
zero-length post-buffer interval use these same abstract linear maps.
The zero branch outside the finite range is the exact finite-family extension. -/

variable {H V Q Z : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {a b c : ℝ} {d : ℕ}

/-- The complete finite insertion family, with the native trace in copy zero. -/
def preparationBufferedPlainLayer (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps H V a b c)
    (E : Fin (d + 1) → H →ₗ[ℝ] PreparationEnergyPath H V c b c)
    (l : ℕ) : H →ₗ[ℝ] PreparationEnergyPath H V a b c :=
  if l = 0 then preparationBufferedInitialMap hac hcb M.full M.homogeneous
  else if hl : l < d + 1 then
    (preparationPostEnergyExtension hcb).toLinearMap.comp (E ⟨l, hl⟩)
  else 0

/-- Every selected copy keeps its post-buffer trace and higher class, and
its insertion defect is the actual post-buffer difference. -/
def BufferedPlainLayerJoinStatement (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps H V a b c)
    (E : Fin (d + 1) → H →ₗ[ℝ] PreparationEnergyPath H V c b c) : Prop :=
  preparationBufferedPlainLayer hac hcb M E 0 =
      preparationBufferedInitialMap hac hcb M.full M.homogeneous ∧
  (∀ (l : Fin (d + 1)) (f : H),
    (preparationBufferedPlainLayer hac hcb M E l f).2 = (E l f).2 ∧
    ∀ (t : Set.Icc a b) (ht : c ≤ (t : ℝ)),
      (preparationBufferedPlainLayer hac hcb M E l f).1 t =
        (E l f).1 ⟨t, ht, t.property.2⟩) ∧
  ∀ (l : ℕ) (hl : l < d) (f : H),
    preparationBufferedPlainLayer hac hcb M E (l + 1) f -
      preparationBufferedKernelMap hcb M.source
        (preparationBufferedPlainLayer hac hcb M E l f) =
    preparationPostEnergyExtension hcb
      (E ⟨l + 1, Nat.succ_lt_succ hl⟩ f -
        M.source (E ⟨l, hl.trans (Nat.lt_succ_self d)⟩ f).2)

/-- Glue the SAME actual paths; only their proved initial values and the
zero-copy homogeneous identity enter this algebraic construction. -/
theorem buffered_plain_layer_join (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps H V a b c)
    (E : Fin (d + 1) → H →ₗ[ℝ] PreparationEnergyPath H V c b c)
    (hhom : ∀ f, (M.homogeneous f).1 ⟨c, le_rfl, hcb⟩ = f)
    (hzero : ∀ f, E 0 f = M.homogeneous ((M.full f).1 ⟨c, hac, hcb⟩))
    (hpositive : ∀ (l : Fin (d + 1)), l ≠ 0 →
      ∀ f, (E l f).1 ⟨c, le_rfl, hcb⟩ = 0) :
    BufferedPlainLayerJoinStatement hac hcb M E := by
  have hcopy (l : Fin (d + 1)) (f : H) :
      (preparationBufferedPlainLayer hac hcb M E l f).2 = (E l f).2 ∧
      ∀ (t : Set.Icc a b) (ht : c ≤ (t : ℝ)),
        (preparationBufferedPlainLayer hac hcb M E l f).1 t =
          (E l f).1 ⟨t, ht, t.property.2⟩ := by
    by_cases hl : l = 0
    · subst l
      constructor
      · change (M.homogeneous ((M.full f).1 ⟨c, hac, hcb⟩)).2 = (E 0 f).2
        rw [hzero]
      · intro t ht
        change (preparationBufferedInitialMap hac hcb M.full M.homogeneous f).1 t = _
        rw [preparation_buffered_initial_after hac hcb M.full M.homogeneous hhom f t ht,
          hzero]
    · have hlval : (l : ℕ) ≠ 0 := fun hv => hl (Fin.ext hv)
      have he : preparationBufferedPlainLayer hac hcb M E l f =
          preparationPostEnergyExtension hcb (E l f) := by
        simp only [preparationBufferedPlainLayer, ite_eq_right hlval, dite_eq_left l.isLt,
          LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [he]
      refine ⟨rfl, ?_⟩
      intro t ht
      change preparationPostExtension hcb (E l f).1 t = _
      rw [preparation_post_extension_after hcb _ t ht, hpositive l hl f, sub_zero]
  refine ⟨by rw [preparationBufferedPlainLayer, ite_eq_left rfl], hcopy, ?_⟩
  intro l hl f
  have hn : l + 1 ≠ 0 := Nat.succ_ne_zero l
  have hlt : l + 1 < d + 1 := Nat.succ_lt_succ hl
  rw [preparationBufferedPlainLayer, ite_eq_right hn, dite_eq_left hlt]
  change preparationPostEnergyExtension hcb (E ⟨l + 1, hlt⟩ f) -
    preparationPostEnergyExtension hcb
      (M.source (preparationBufferedPlainLayer hac hcb M E l f).2) = _
  rw [(hcopy ⟨l, hl.trans (Nat.lt_succ_self d)⟩ f).1, ← map_sub]

/-- A positive-copy price on the post-buffer interval is also its whole-window
insertion-defect price, without an extension factor. -/
theorem buffered_plain_layer_defect_energy_le (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps H V a b c)
    (E : Fin (d + 1) → H →ₗ[ℝ] PreparationEnergyPath H V c b c)
    (hjoin : BufferedPlainLayerJoinStatement hac hcb M E)
    (hpositive : ∀ (l : Fin (d + 1)), l ≠ 0 →
      ∀ f, (E l f).1 ⟨c, le_rfl, hcb⟩ = 0)
    (hsource : ∀ U, (M.source U).1 ⟨c, le_rfl, hcb⟩ = 0)
    (L : H →L[ℝ] Q) (G : V →L[ℝ] Z) (ν : ℝ)
    (l : ℕ) (hl : l < d) (f : H) :
    preparationPathEnergy a b c L G ν
      (preparationBufferedPlainLayer hac hcb M E (l + 1) f -
        preparationBufferedKernelMap hcb M.source
          (preparationBufferedPlainLayer hac hcb M E l f)) ≤
    preparationPathEnergy c b c L G ν
      (E ⟨l + 1, Nat.succ_lt_succ hl⟩ f -
        M.source (E ⟨l, hl.trans (Nat.lt_succ_self d)⟩ f).2) := by
  rw [hjoin.2.2 l hl f]
  apply preparation_post_energy_extension_le
  change (E ⟨l + 1, Nat.succ_lt_succ hl⟩ f).1 ⟨c, le_rfl, hcb⟩ -
    (M.source _).1 ⟨c, le_rfl, hcb⟩ = 0
  have hn : (⟨l + 1, Nat.succ_lt_succ hl⟩ : Fin (d + 1)) ≠ 0 := by
    intro he
    exact Nat.succ_ne_zero l (congrArg Fin.val he)
  rw [hpositive _ hn f, hsource, sub_self]

/-- Reading the whole finite insertion family after the buffer gives exactly
its actual plain-chain readout, with no initial-value correction. -/
theorem buffered_plain_layer_sum_after (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps H V a b c)
    (E : Fin (d + 1) → H →ₗ[ℝ] PreparationEnergyPath H V c b c)
    (hjoin : BufferedPlainLayerJoinStatement hac hcb M E)
    (f : H) (t : Set.Icc a b) (ht : c ≤ (t : ℝ)) :
    (∑ l ∈ Finset.range (d + 1), preparationBufferedPlainLayer hac hcb M E l f).1 t =
      ∑ l : Fin (d + 1), (E l f).1 ⟨t, ht, t.property.2⟩ := by
  let T := (ContinuousMap.evalCLM ℝ t).toLinearMap.comp
    (ContinuousLinearMap.fst ℝ C(Set.Icc a b, H)
      (Lp V 2 (volume.restrict (Set.Icc c b)))).toLinearMap
  change T (∑ l ∈ Finset.range (d + 1), preparationBufferedPlainLayer hac hcb M E l f) = _
  rw [← Fin.sum_univ_eq_sum_range, map_sum]
  exact Finset.sum_congr rfl (fun l _ => (hjoin.2.1 l f).2 t ht)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual buffered maps are chosen before the mass used to price them.
Equality of the physical coefficients, inclusions and kernels transfers all
three PDE realizations. The weights and Schur budgets may then vary.

The degenerate cases are included: empty and singleton families, identity geometry, order zero,
zero data, edgeless seeds and zero-length windows retain exactly the same
maps. No positivity of theta is asserted for an empty family; the price is
7 times its absolute value. The agreement premise concerns physical data,
not an estimate or a solution supplied as an extra hypothesis. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul
  preparationWeightedLowSMul preparationWeightedLowSpace
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν c : ℝ} {D : ℕ}

/-- Two mass budgets describe the same physical kernel equation. -/
def PreparationKernelDataAgreement
    (P Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D) : Prop :=
  P.B = Q.B ∧ P.C = Q.C ∧ P.S = Q.S

/-- Transfer the realizations, without replacing any of the three maps. -/
def KernelMapMassTransferStatement
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (hac : a ≤ c) (hcb : c ≤ b) : Prop :=
  ∀ Q, PreparationKernelDataAgreement P Q → ∀ M,
    BufferedKernelMapsRealizes P φ hac hcb M → BufferedKernelMapsRealizes Q φ hac hcb M

/-- Canonical regularized carriers depend only on the actual inclusion and kernel. -/
theorem preparation_kernel_lift_eq
    (P Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hPQ : PreparationKernelDataAgreement P Q)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk 1 (h i)) :
    P.lift t ht V = Q.lift t ht V := by
  funext i j α
  apply TorusHk.ext_value
  rw [P.lift_value, Q.lift_value, hPQ.2.1, hPQ.2.2]

/-- The canonical flux is independent of the mass used to certify its bound. -/
theorem preparation_kernel_flux_eq
    (P Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hPQ : PreparationKernelDataAgreement P Q)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk 1 (h i)) (i : ι) :
    P.flux t ht V i = Q.flux t ht V i := by
  classical
  have he : P.rawFlux t ht V i = Q.rawFlux t ht V i := by
    unfold KernelEnergy.TorusKernelOperator.rawFlux
    rw [hPQ.1, preparation_kernel_lift_eq P Q hPQ]
  apply KernelEnergy.torusCarrier_eq_of_value_ae
  exact (P.flux_raw t ht V i).trans (he ▸ (Q.flux_raw t ht V i).symm)

/-- Agreement survives clamping, including times outside the solution window. -/
theorem preparation_clamped_kernel_mass_eq
    (P Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hPQ : PreparationKernelDataAgreement P Q) (i : ι) (t : ℝ)
    (U : CoupledHighHilbert (h := h) (fun _ => 0)) :
    P.clampedAmbientFluxCLM i t U = Q.clampedAmbientFluxCLM i t U := by
  change P.flux (Set.projIcc a b P.htime t) _
    (KernelEnergy.TorusKernelOperator.ambientCarrierCLM (h := h) (k := 0) U) i =
    Q.flux (Set.projIcc a b Q.htime t) _
    (KernelEnergy.TorusKernelOperator.ambientCarrierCLM (h := h) (k := 0) U) i
  exact preparation_kernel_flux_eq P Q hPQ _ _ _ i

/-- The actual source datum, including its off-window representative, is unchanged. -/
theorem preparation_kernel_scalar_mass_eq
    (P Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (hPQ : PreparationKernelDataAgreement P Q) :
    preparationKernelScalarDatum P = preparationKernelScalarDatum Q := by
  funext i U
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext t
    exact preparation_clamped_kernel_mass_eq P Q hPQ i t (U t)

/-- The physical native and scalar equations transfer to the new mass unchanged. -/
theorem kernel_map_mass_transfer
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (hac : a ≤ c) (hcb : c ≤ b) :
    KernelMapMassTransferStatement P φ hac hcb := by
  intro Q hPQ M hM
  refine ⟨?_, hM.2.1, ?_⟩
  · intro f
    obtain ⟨W, Y, hs, hW⟩ := hM.1 f
    refine ⟨W, Y, ?_, hW⟩
    simpa only [hPQ.1, hPQ.2.1, hPQ.2.2] using hs
  · let P' := Buffer.kernelOperator_time_restrict P (Set.Icc_subset_Icc hac le_rfl) hcb
    let Q' := Buffer.kernelOperator_time_restrict Q (Set.Icc_subset_Icc hac le_rfl) hcb
    have he : PreparationKernelDataAgreement P' Q' := hPQ
    have hx := preparation_kernel_scalar_mass_eq P' Q' he
    change ScalarFamilyEnergyPathRealizes (ν := ν) hcb (streamVel φ)
      (preparationKernelScalarDatum Q') M.source
    rw [← hx]
    exact hM.2.2

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The energy rows of the SAME supplied native/scalar maps, at every
certified mass, in the order-zero physical norm. This joins already proved
mass transfer, native energy, scalar insertion and trace contraction; it
selects no new evolution, representative, buffer datum or weight-specific map.
The degenerate cases are included: empty and singleton families, D=2, zero/negative Theta (absolute
value retained), identity geometry, constants, edgeless families and c=b use the same rows.
No conclusion is inferred from nontriviality of a component or a datum. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul
  preparationWeightedLowSMul preparationWeightedLowSpace

/-- The fixed native map, scalar source and trace have all three required
weighted energy rows, with literal constants 2, 7*abs(Theta), and 1. -/
def SuppliedNativeWeightedEnergyStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*}
    [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
    [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
    [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
    {a b ρ ν c : ℝ} {D Kmax : ℕ}
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ), IsAdmissibleStream φ →
    ∀ (hac : a ≤ c) (hcb : c ≤ b),
    Providers.WeakGen.Comparison.TorusDriftData ν ρ c b (streamVel φ) Kmax →
    ∀ (π : ι → ℝ) (weights : Set (ι → ℝ))
      (operators : ∀ w ∈ weights,
        KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
      (Θ : ℝ),
    (∀ w hw, PreparationKernelDataAgreement P (operators w hw)) →
    (∀ w hw, (operators w hw).π = fun i => π i / w i ^ 2) →
    (∀ w hw, (operators w hw).θ = Θ) →
    ∀ M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c,
    BufferedKernelMapsRealizes P φ hac hcb M →
    ∀ w ∈ weights,
      let πw := fun i => π i / w i ^ 2
      (∀ f, preparationWeightedPathEnergy (h := h) ρ πw ν a b c (M.full f) ≤
        2 * Real.sqrt (massNormSq 1 πw (fun i => (f i).val))) ∧
      (∀ x, preparationWeightedPathEnergy (h := h) ρ πw ν a b c
        (preparationBufferedKernelMap hcb M.source x) ≤
        7 * |Θ| * preparationWeightedPathEnergy (h := h) ρ πw ν a b c x) ∧
      (∀ (x : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
          (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) (t : Set.Icc a b),
        Real.sqrt (massNormSq 1 πw (fun i => (x.1 t i).val)) ≤
          preparationWeightedPathEnergy (h := h) ρ πw ν a b c x)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Energy bounds for the same supplied buffered maps at every certified mass.
Only the PDE realizations are transferred; no new path or representative is chosen.
The order-zero mass identity restores the literal radius-one input and trace norms. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul
  preparationWeightedLowSMul preparationWeightedLowSpace

/-- The supplied full map, insertion and trace obey the exact three energy rows
at every certified weight, with constants two, seven times the absolute budget,
and one, respectively. -/
theorem supplied_native_weighted_energy : SuppliedNativeWeightedEnergyStatement := by
  intro ι _ _ h _ _ _ _ _ _ Γ _ G _ _ _ _ _ _ a b ρ ν c D Kmax
    P φ hφ hac hcb hd π weights operators Θ hagree hmass htheta M hM w hw
  let Q := operators w hw
  have hQ : BufferedKernelMapsRealizes Q φ hac hcb M :=
    kernel_map_mass_transfer P φ hac hcb Q (hagree w hw) M hM
  have hmassQ : Q.π = fun i => π i / w i ^ 2 := hmass w hw
  have hthetaQ : Q.θ = Θ := htheta w hw
  have hπw : ∀ i, 0 < π i / w i ^ 2 := by
    intro i
    rw [← congrFun hmassQ i]
    exact Q.hπ i
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro f
    have hf := native_path_energy_bound Q hφ hac M.full hQ.1 f
    simpa only [hmassQ, CycleJointProofs.massNormSq_order_zero] using hf
  · intro x
    have hx := kernel_insertion_energy_bound Q hac hcb hd M hQ x
    simpa only [hmassQ, hthetaQ] using hx
  · intro x t
    have ht := preparation_weighted_trace_le_energy ρ (fun i => π i / w i ^ 2)
      hπw ν a b c x t
    simpa only [CycleJointProofs.massNormSq_order_zero] using ht

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! One higher buffered datum for all certified masses of the same kernel
operator. The operator tower and the linear low evolution are existing
objects; the rough kernel buffer supplies their higher values at
the prescribed delay. Injective truncation makes the choice linear and
transfers every mass bound to the same map.

The degenerate cases are included: K=0, empty and singleton families, zero/constants, trivial
fibres, identity geometry and edgeless seeds. The delay is supplied explicitly,
independently of a preparation pair or a nonempty component type. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν : ℝ} {Dm K : ℕ}

/-- The actual same-data kernel tower, its linear evolution, and the numeric
molecular delay. These are the inputs of the rough buffer theorem. -/
structure PreparationKernelBufferFrame
    (P : KernelEnergy.TorusKernelOperator (h := h)
      (Γ := Γ) (G := G) a b ρ ν 0 Dm) (OC : OCData) (m K : ℕ) where
  delay : ℝ
  delay_pos : 0 < delay
  delay_end : a + delay ≤ b
  radius_delay : ρ ^ 2 ≤ (5 * ν / 4) * delay
  π : ι → ℝ
  weights : Set (ι → ℝ)
  unit_weight : (fun _ => 1) ∈ weights
  operators : ∀ w ∈ weights, (j : Fin (K + 1)) →
    KernelEnergy.TorusKernelOperator (h := h)
      (Γ := Γ) (G := G) a b ρ ν j.val Dm
  mass : ∀ w hw j, (operators w hw j).π = fun i => π i / w i ^ 2
  coefficient : ∀ w hw j, (operators w hw j).B = P.B
  inclusion : ∀ w hw j, (operators w hw j).C = P.C
  kernel : ∀ w hw j, (operators w hw j).S = P.S
  slow : ℝ
  alpha_pos : 0 < OC.α
  alpha_lt : OC.α < 1 / 3
  slow_pos : 0 < slow
  slow_lt : slow < (1 - OC.α) / 2
  admissible_q : IsAdmissibleQ OC.α slow OC.q
  profile : IsFastProfile OC.ζ
  frequency : 128 ≤ OC.Λ
  stream : IsOCStreamSeq OC.α OC.q OC.Λ OC.ζ OC.Φ
  level_pos : 1 ≤ m
  radius_small : 1024 * ρ / OC.eps m ≤ 1 / 2
  strain_small : (Buffer.actualDriftJetConstant * ocA OC.α OC.q OC.Λ m) * 1024 * ρ ^ 2 ≤ ν / 8
  trace : (∀ i : ι, TorusHk 0 (h i)) →ₗ[ℝ]
    (∀ i : ι, ℝ → TorusHk 0 (h i))
  solution : ∀ f, ∃ w : ∀ i : ι, ℝ → TorusHk 1 (h i),
    ∃ y : ∀ i j (γ : Γ i j), ℝ → TorusHk (0 + Dm - 1) (G i j γ),
      IsKernelWeakSolutionTorus ν a b (streamVel (OC.Φ m)) 0 Dm P.B P.C P.S f
        (fun _ _ => 0) (fun _ _ => 0) (trace f) w y

variable {P : KernelEnergy.TorusKernelOperator (h := h)
  (Γ := Γ) (G := G) a b ρ ν 0 Dm} {OC : OCData} {m : ℕ}

/-- One actual high datum at the prescribed buffer, before every mass in
weights. Its cost is the existing order-only molecular buffer cost. The mass norm
is generic in the fibres; weighted_buffer_readout converts it at the root
instance without a root-indexed linear-map signature. -/
def KernelBufferedHigherTraceStatement (F : PreparationKernelBufferFrame P OC m K) : Prop :=
  ∃ B : (∀ i : ι, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i : ι, TorusHk K (h i)),
    (∀ f i, truncateTorusHk (Nat.zero_le K) (B f i) = F.trace f i (a + F.delay)) ∧
    ∀ w ∈ F.weights, ∀ f,
      Real.sqrt (massNormSq ρ (fun i => F.π i / w i ^ 2) (fun i => (B f i).val)) ≤
        Real.sqrt (Buffer.bufferEnergyCost K *
          massNormSq ρ (fun i => F.π i / w i ^ 2) (fun i => (f i).val))

private theorem preparation_kernel_buffered_value
    (F : PreparationKernelBufferFrame P OC m K)
    (w : ι → ℝ) (hw : w ∈ F.weights)
    (f : ∀ i : ι, TorusHk 0 (h i)) :
    ∃ u : ∀ i : ι, TorusHk K (h i),
      (∀ i, truncateTorusHk (Nat.zero_le K) (u i) = F.trace f i (a + F.delay)) ∧
      Real.sqrt (massNormSq ρ (fun i => F.π i / w i ^ 2) (fun i => (u i).val)) ≤
        Real.sqrt (Buffer.bufferEnergyCost K *
          massNormSq ρ (fun i => F.π i / w i ^ 2) (fun i => (f i).val)) := by
  obtain ⟨W, Y, hs⟩ := F.solution f
  let PP := F.operators w hw
  let P0 := PP ⟨0, Nat.zero_lt_succ K⟩
  have hs0 : IsKernelWeakSolutionTorus ν a b (streamVel (OC.Φ m)) 0 Dm
      P0.B P0.C P0.S f (fun _ _ => 0) (fun _ _ => 0) (F.trace f) W Y := by
    rw [F.coefficient w hw ⟨0, Nat.zero_lt_succ K⟩,
      F.inclusion w hw ⟨0, Nat.zero_lt_succ K⟩, F.kernel w hw ⟨0, Nat.zero_lt_succ K⟩]
    exact hs
  have he : 0 < ocEpsilon OC.q OC.Λ m :=
    (Scales.epsilon_basic F.admissible_q.1 F.frequency).1
  have ha : 0 < ocA OC.α OC.q OC.Λ m := Real.rpow_pos_of_pos he _
  have hcur := Velocity.streamSeq_admissible F.profile F.frequency F.stream m
  obtain ⟨hv, hvp, hd, hbd, hmeas⟩ := Buffer.stream_kernel_drift_data hcur a b
  have hb := Buffer.kernel_rough_solution_buffer (h := h) PP P0 rfl
    (fun i => F.π i / w i ^ 2) (F.mass w hw)
    (fun j => (F.coefficient w hw j).trans (F.coefficient w hw (Fin.last K)).symm)
    (fun j => (F.inclusion w hw j).trans (F.inclusion w hw (Fin.last K)).symm)
    (fun j => (F.kernel w hw j).trans (F.kernel w hw (Fin.last K)).symm)
    F.delay_pos F.delay_end F.radius_delay (streamVel (OC.Φ m)) hv hvp
    (Buffer.actualDriftJetConstant * ocA OC.α OC.q OC.Λ m) 1024 (ocEpsilon OC.q OC.Λ m)
    (mul_nonneg Buffer.actualDriftJetConstant_nonneg ha.le) (by norm_num) he
    F.radius_small F.strain_small hd
    (fun t _ l hl _ x => Buffer.actual_stream_drift_arrays OC.α F.slow
      F.alpha_pos F.alpha_lt F.slow_pos F.slow_lt OC.q F.admissible_q OC.ζ F.profile
      OC.Λ F.frequency OC.Φ F.stream m F.level_pos t l hl x)
    hbd hmeas f (F.trace f) W Y hs0
  exact hb K le_rfl (a + F.delay) ⟨le_rfl, F.delay_end⟩

/-- The existing rough buffer and linear range restriction produce the SAME
buffered high datum for every mass certificate, with no second PDE choice. -/
theorem kernel_buffered_higher_trace
    (F : PreparationKernelBufferFrame P OC m K) : KernelBufferedHigherTraceStatement F := by
  classical
  let L : (∀ i : ι, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i : ι, TorusHk 0 (h i)) :=
    { toFun := fun f i => F.trace f i (a + F.delay)
      map_add' := fun f g => by
        funext i
        exact congrFun (congrFun (F.trace.map_add f g) i) (a + F.delay)
      map_smul' := fun r f => by
        funext i
        exact congrFun (congrFun (F.trace.map_smul r f) i) (a + F.delay) }
  let hbuffer := preparation_kernel_buffered_value F
  have hrep : HigherTraceRepresentativesStatement (h := h) K L := by
    intro f
    obtain ⟨u, hu, _⟩ := hbuffer (fun _ => 1) F.unit_weight f
    exact ⟨u, hu⟩
  obtain ⟨B, hB, hbound⟩ := higher_buffered_trace_map_of_representatives K L hrep
  refine ⟨B, hB, ?_⟩
  intro w hw
  have hb := hbound
    (fun u => Real.sqrt (massNormSq ρ (fun i => F.π i / w i ^ 2) (fun i => (u i).val)))
    (fun f => Real.sqrt (Buffer.bufferEnergyCost K *
      massNormSq ρ (fun i => F.π i / w i ^ 2) (fun i => (f i).val))) 1
    (by
      intro f
      obtain ⟨u, hu, he⟩ := hbuffer w hw f
      exact ⟨u, hu, by simpa only [one_mul] using he⟩)
  simpa only [one_mul] using hb

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The finite physical insertion family gives the common preparation route.
Its full and kernel maps are the already realized buffered maps, and its
plain readout is the sum of the SAME post-buffer copies. This adapter makes
no PDE choice and introduces no mass-specific route.

The degenerate cases are included: depth zero is exactly scalar restart; empty and singleton
families, zero/constants, D=2, identity geometry, edgeless seeds and degenerate windows
use the same formula. Clamping only extends a continuous trace off its window. The linear
coordinate identification may be the identity; no root-specific Sobolev
instance is searched through the path construction. -/

/-- The already selected post-buffer maps of the finite plain chain. -/
abbrev PreparationPostPlainMaps (H V : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (c b : ℝ) :=
  Fin (d + 1) → H →ₗ[ℝ] PreparationEnergyPath H V c b c

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- One physical route from the actual full path, scalar source map and
finite plain chain. The entire construction precedes the datum and masses. -/
def preparationBufferedInsertionRoute (F : Request hr D Dm bw j₀)
    (e : F.Data 0 ≃ₗ[ℝ] H)
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
    (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf) :
    F.InsertionRoute (PreparationEnergyPath H V F.s F.tf F.bufferEnd) where
  full := M.full.comp e.toLinearMap
  initial := (preparationBufferedInitialMap hac hcb M.full M.homogeneous).comp e.toLinearMap
  kernel := preparationBufferedKernelMap hcb M.source
  layer := fun l => (preparationBufferedPlainLayer hac hcb M E l).comp e.toLinearMap
  trace := fun t => e.symm.toLinearMap.comp
    ((ContinuousMap.evalCLM ℝ (Set.projIcc F.s F.tf (hac.trans hcb) t)).toLinearMap.comp
      (ContinuousLinearMap.fst ℝ _ _).toLinearMap)

/-- The finite physical route has the proved fixed point and the actual
post-buffer plain readout. This leaves no restart or finite-sum leaf open. -/
def BufferedInsertionRouteStatement (F : Request hr D Dm bw j₀)
    (e : F.Data 0 ≃ₗ[ℝ] H)
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
    (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf) : Prop :=
  let R := preparationBufferedInsertionRoute F e hac hcb M E
  F.ScalarRestartStatement R ∧
    (∀ (f : F.Data 0) (t : ℝ) (ht : t ∈ Set.Icc F.bufferEnd F.tf),
      R.plainTrace t f = e.symm (∑ l : Fin (F.Hpr + 1), (E l (e f)).1 ⟨t, ht⟩)) ∧
    (∀ (x : PreparationEnergyPath H V F.s F.tf F.bufferEnd) (t : ℝ),
      R.trace t x = e.symm (x.1 (Set.projIcc F.s F.tf (hac.trans hcb) t)))

/-- Transport the generic layer join once to the actual stage data.
The restart is the existing full fixed point, not an assumed approximation. -/
theorem buffered_insertion_route (F : Request hr D Dm bw j₀)
    (e : F.Data 0 ≃ₗ[ℝ] H)
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
    (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf)
    (hfixed : M.IsFixedPoint hac hcb)
    (hjoin : BufferedPlainLayerJoinStatement hac hcb M E) :
    BufferedInsertionRouteStatement F e hac hcb M E := by
  refine ⟨⟨fun f => hfixed (e f), ?_⟩, ?_, fun _ _ => rfl⟩
  · exact congrArg (fun A => A.comp e.toLinearMap) hjoin.1
  · intro f t ht
    have ht' : t ∈ Set.Icc F.s F.tf := ⟨hac.trans ht.1, ht.2⟩
    have hs := buffered_plain_layer_sum_after hac hcb M E hjoin (e f) ⟨t, ht'⟩ ht.1
    change e.symm ((∑ l ∈ Finset.range (F.Hpr + 1),
      preparationBufferedPlainLayer hac hcb M E l (e f)).1
        (Set.projIcc F.s F.tf (hac.trans hcb) t)) = _
    rw [Set.projIcc_of_mem (hac.trans hcb) ht']
    exact congrArg e.symm hs

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual physical buffered route solves the original native equation
and satisfies the exact finite fixed point/restart. All maps are the supplied
native/scalar/copy maps; there is no second evolution or mass-dependent path.
The degenerate cases are included: empty and singleton families, Hpr=0, Dm=2, constants, identity
geometry and an edgeless seed keep the same entire-window trace and post-buffer higher class. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- One physical route has the actual native weak equation and exact
restart, using the same buffered maps and genuine finite copy paths. -/
theorem preparation_physical_route_realized (F : Request hr D Dm bw j₀)
    {Kbuf : ℕ} {CK : ℕ → ℝ} {Θ : ℝ} (T : PreparationNativeTower F Kbuf CK Θ)
    (hac : F.s ≤ F.bufferEnd) (hcb : F.bufferEnd ≤ F.tf)
    {H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : F.Data 0 ≃ₗ[ℝ] H)
    (M : PreparationBufferedMaps H V F.s F.tf F.bufferEnd)
    (E : PreparationPostPlainMaps H V F.Hpr F.bufferEnd F.tf)
    (hNative : ∀ f : F.Data 0,
      ∃ (W : ∀ v : CompIn F.G.comps, ℝ → TorusHk 1 (hr v.1.root))
        (Y : ∀ v u (_γ : F.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
        let P := T.operators (fun _ => 1) (Or.inl rfl) ⟨0, Nat.succ_pos _⟩
        IsKernelWeakSolutionTorus (D.κ F.G.level) F.s F.tf (streamVel (D.Φ F.G.level))
          0 Dm P.B P.C P.S f (fun _ _ => 0) (fun _ _ => 0)
          (fun v t => e.symm ((M.full (e f)).1 (Set.projIcc F.s F.tf (hac.trans hcb) t)) v) W Y)
    (hfixed : M.IsFixedPoint hac hcb)
    (hjoin : BufferedPlainLayerJoinStatement hac hcb M E) :
    let R := preparationBufferedInsertionRoute F e hac hcb M E
    F.RealizedEvolutionStatement R ∧ F.ScalarRestartStatement R := by
  refine ⟨?_, (buffered_insertion_route F e hac hcb M E hfixed hjoin).1⟩
  intro f
  obtain ⟨W, Y, hs⟩ := hNative f
  refine ⟨W, Y, ?_⟩
  dsimp only at hs
  rw [T.coefficient, T.inclusion, T.kernel] at hs
  change IsKernelWeakSolutionTorus (D.κ F.G.level) F.s F.tf (streamVel (D.Φ F.G.level))
    0 Dm (fun v u γ d => F.G.physCoeff v u γ d.1)
    (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
    (F.G.sysS F.P F.seedK F.freshK F.φ₀ F.hφ₀)
    f (fun _ _ => 0) (fun _ _ => 0)
    (fun v t => e.symm ((M.full (e f)).1 (Set.projIcc F.s F.tf (hac.trans hcb) t)) v) W Y
  exact hs

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Proof of `NativeConstantTraceStatement`: a realized native path fixes componentwise
constants. The constant path is a weak solution (`const_weak_solution`), and the
order-zero uniqueness `preparation_kernel_order_zero_unique` identifies it with the realized
path. No replacement evolution is chosen.

The degenerate cases are included: empty families, singleton families, `D = 2`, a one-point window
and the zero datum are all covered by the general argument. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν : ℝ} {D : ℕ}

/-- Every realized native trace fixes componentwise spatial constants at every time. -/
theorem nativeConstantTrace :
    ∀ (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
      (φ : ℝ → Vec 2 → ℝ) (c : ℝ), NativeConstantTraceStatement P φ c := by
  intro P φ c hφ L hL f cv hcv t
  have hf : ∀ i, f i = ConstHk 0 (cv i) := fun i => eq_constHk_of_jet (hcv i)
  obtain ⟨w, y, hs, _⟩ := hL f
  have hc := const_weak_solution P (streamVel φ) f cv hf
  have hu := preparation_kernel_order_zero_unique P hφ f (fun i _ => f i)
    (fun i s => (L f).1 (Set.projIcc a b P.htime s) i) _ w _ y hc hs
  funext i
  have := hu i t t.2
  rw [Set.projIcc_val] at this
  exact this.symm
end

/-! The actual native constant trace fixes the SAME higher buffered datum.
This is precisely the cv/f/initial-constant/output-constant quantifier order
of the copied-family model's hBconst clause. The only buffer input is the
already constructed map's literal low-trace identity at the buffer time.

The degenerate cases are included: empty and singleton families, diagonal sources, D=2,
zero/constants, identity geometry, edgeless seeds and a one-point window use the same equality.
There is no extra smoothness assumption or a new choice of evolution. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν c : ℝ} {D : ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- Exact constant-data clause of the copied model for its actual higher datum. -/
def BufferedConstantTraceStatement (K : ι → ℕ)
    (B : (∀ i, TorusHk 0 (h i)) → ∀ i, TorusHk (K i) (h i)) : Prop :=
  ∀ (cv : ∀ i, h i) (f : ∀ i, TorusHk 0 (h i)),
    (∀ i, (f i).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
      fun _ => cv i) →
    ∀ i, (truncateTorusHk (Nat.zero_le (K i)) (B f i)).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict unitCube] fun _ => cv i

/-- The actual trace theorem discharges hBconst using the SAME buffered
higher map and its proved truncation identity. -/
theorem buffered_constant_trace_of_native
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (L : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hreal : NativeEnergyPathRealizes P φ c L)
    (K : ι → ℕ) (B : (∀ i, TorusHk 0 (h i)) → ∀ i, TorusHk (K i) (h i))
    (t : Set.Icc a b)
    (hB : ∀ f i, truncateTorusHk (Nat.zero_le (K i)) (B f i) = (L f).1 t i) :
    BufferedConstantTraceStatement K B := by
  intro cv f hf i
  have hc := nativeConstantTrace P φ c hφ L hreal f cv hf t
  rw [hB f i, hc]
  exact hf i
end

/-! Assembly of one native buffered datum from its actual path and operator
tower. One further input constructs the existing rough-buffer frame with
the same path at delay rho^2/nu. Its numeric cap is already fixed by the
scalar molecular-radius theorem, independently of all type and data
choices. The higher representative, all its mass bounds and its constant
clause are discharged here from the existing theorems.

A buffer ending exactly at b is allowed. Positive radius and diffusivity ensure a positive
delay. No seed radius improvement, extra
stored-order cap, separate mass-dependent path or new PDE is assumed. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν c : ℝ} {Dm : ℕ}

/-- Existing scalar environment, operator tower and actual path. The tower
is produced elsewhere; this input imposes no bound on K by stored seed orders. -/
structure PreparationNativeBufferInput
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 Dm)
    (OC : OCData) (m K : ℕ) (π : ι → ℝ) (weights : Set (ι → ℝ)) where
  slow : ℝ
  alpha_pos : 0 < OC.α
  alpha_lt : OC.α < 1 / 3
  slow_pos : 0 < slow
  slow_lt : slow < (1 - OC.α) / 2
  admissible_q : IsAdmissibleQ OC.α slow OC.q
  profile : IsFastProfile OC.ζ
  frequency : 128 ≤ OC.Λ
  stream : IsOCStreamSeq OC.α OC.q OC.Λ OC.ζ OC.Φ
  level_pos : 1 ≤ m
  c₀ : ℝ
  c₀_pos : 0 < c₀
  radius_cap : c₀ ≤ Buffer.exists_molecular_uniform_constants.choose
  radius_formula : ρ = c₀ * min (OC.eps m) (Real.sqrt (ν / ocA OC.α OC.q OC.Λ m))
  delay_end : a + ρ ^ 2 / ν ≤ b
  unit_weight : (fun _ => 1) ∈ weights
  operators : ∀ w ∈ weights, (j : Fin (K + 1)) →
    KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν j.val Dm
  mass : ∀ w hw j, (operators w hw j).π = fun i => π i / w i ^ 2
  coefficient : ∀ w hw j, (operators w hw j).B = P.B
  inclusion : ∀ w hw j, (operators w hw j).C = P.C
  kernel : ∀ w hw j, (operators w hw j).S = P.S
  path : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
    PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c
  realizes : NativeEnergyPathRealizes P (OC.Φ m) c path

/-- Exact frame output: the molecular delay, the supplied masses and the
literal clamped time trace of the same actual native path. -/
def NativeKernelBufferFrameStatement
    {P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 Dm}
    {OC : OCData} {m K : ℕ} {π : ι → ℝ} {weights : Set (ι → ℝ)}
    (I : PreparationNativeBufferInput (c := c) P OC m K π weights) : Prop :=
  ∃ F : PreparationKernelBufferFrame P OC m K,
    F.delay = ρ ^ 2 / ν ∧ F.π = π ∧ F.weights = weights ∧
    ∀ f i t, F.trace f i t = (I.path f).1 (Set.projIcc a b P.htime t) i

/-- Bounded frame-construction leaf, generic in every actual path and tower.
All scalar smallness follows from the already proved radius cap. -/
def NativeKernelBufferFrameProductionStatement : Prop :=
  ∀ (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 Dm)
    (OC : OCData) (m K : ℕ) (π : ι → ℝ) (weights : Set (ι → ℝ))
    (I : PreparationNativeBufferInput (c := c) P OC m K π weights),
    NativeKernelBufferFrameStatement I

/-- Higher buffering and the trace theorem discharge all remaining datum clauses for
the same frame, map and path; only the bounded frame leaf is conditional. -/
theorem native_buffered_datum_of_frame
    {P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 Dm}
    {OC : OCData} {m K : ℕ} {π : ι → ℝ} {weights : Set (ι → ℝ)}
    (I : PreparationNativeBufferInput (c := c) P OC m K π weights)
    (hframe : NativeKernelBufferFrameStatement I) :
    ∃ B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk K (h i)),
      (∀ f i, truncateTorusHk (Nat.zero_le K) (B f i) =
        (I.path f).1 (Set.projIcc a b P.htime (a + ρ ^ 2 / ν)) i) ∧
      (∀ w ∈ weights, ∀ f,
        Real.sqrt (massNormSq ρ (fun i => π i / w i ^ 2) (fun i => (B f i).val)) ≤
          Real.sqrt (Buffer.bufferEnergyCost K *
            massNormSq ρ (fun i => π i / w i ^ 2) (fun i => (f i).val))) ∧
      BufferedConstantTraceStatement (fun _ => K) B := by
  obtain ⟨F, hdelay, hπ, hweights, htrace⟩ := hframe
  obtain ⟨B, hB, hbound⟩ := kernel_buffered_higher_trace F
  have hlow (f : ∀ i, TorusHk 0 (h i)) (i : ι) :
      truncateTorusHk (Nat.zero_le K) (B f i) =
        (I.path f).1 (Set.projIcc a b P.htime (a + ρ ^ 2 / ν)) i := by
    rw [hB f i, htrace f i, hdelay]
  refine ⟨B, hlow, ?_, ?_⟩
  · simpa only [hπ, hweights] using hbound
  · exact buffered_constant_trace_of_native P (OC.Φ m)
      (Velocity.streamSeq_admissible I.profile I.frequency I.stream m)
      I.path I.realizes (fun _ => K) B
      (Set.projIcc a b P.htime (a + ρ ^ 2 / ν)) hlow
end

/-! The actual path and finite operator tower produce the same molecular-delay buffer frame. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν c : ℝ} {Dm : ℕ}

/-- The original supplied path and tower share one buffer frame at the molecular delay. -/
theorem nativeKernelBufferFrameProduction :
    NativeKernelBufferFrameProductionStatement (h := h) (Γ := Γ) (G := G)
      (a := a) (b := b) (ρ := ρ) (ν := ν) (c := c) (Dm := Dm) := by
  intro P OC m K π weights I
  have he : 0 < OC.eps m := (Scales.epsilon_basic I.admissible_q.1 I.frequency).1
  have ha : 0 < ocA OC.α OC.q OC.Λ m := Real.rpow_pos_of_pos he _
  have hcaps := Buffer.exists_molecular_uniform_constants.choose_spec.2
    I.c₀ I.c₀_pos I.radius_cap
  have hbounds := hcaps.2.2 (OC.eps m) ν (ocA OC.α OC.q OC.Λ m)
    he P.diffusivity_pos ha
  dsimp only at hbounds
  rw [← I.radius_formula] at hbounds
  let trace : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, ℝ → TorusHk 0 (h i)) := {
    toFun := fun f i t => (I.path f).1 (Set.projIcc a b P.htime t) i
    map_add' := by
      intro f g
      funext i t
      exact congrArg (fun z => z.1 (Set.projIcc a b P.htime t) i) (I.path.map_add f g)
    map_smul' := by
      intro r f
      funext i t
      exact congrArg (fun z => z.1 (Set.projIcc a b P.htime t) i) (I.path.map_smul r f) }
  have hdelay : 0 < ρ ^ 2 / ν := div_pos (sq_pos_of_pos P.radius_pos) P.diffusivity_pos
  have hrad : ρ ^ 2 ≤ (5 * ν / 4) * (ρ ^ 2 / ν) := by
    calc
      ρ ^ 2 = (ρ ^ 2 / ν) * ν := (div_mul_cancel₀ _ P.diffusivity_pos.ne').symm
      _ = ν * (ρ ^ 2 / ν) := mul_comm _ _
      _ ≤ (5 * ν / 4) * (ρ ^ 2 / ν) :=
        mul_le_mul_of_nonneg_right (by linarith only [P.diffusivity_pos]) hdelay.le
  let F : PreparationKernelBufferFrame P OC m K := {
    delay := ρ ^ 2 / ν
    delay_pos := hdelay
    delay_end := I.delay_end
    radius_delay := hrad
    π := π
    weights := weights
    unit_weight := I.unit_weight
    operators := I.operators
    mass := I.mass
    coefficient := I.coefficient
    inclusion := I.inclusion
    kernel := I.kernel
    slow := I.slow
    alpha_pos := I.alpha_pos
    alpha_lt := I.alpha_lt
    slow_pos := I.slow_pos
    slow_lt := I.slow_lt
    admissible_q := I.admissible_q
    profile := I.profile
    frequency := I.frequency
    stream := I.stream
    level_pos := I.level_pos
    radius_small := hbounds.2.2.1
    strain_small := hbounds.2.2.2.1
    trace := trace
    solution := by
      intro f
      obtain ⟨w, y, hsol, _⟩ := I.realizes f
      exact ⟨w, y, hsol⟩ }
  exact ⟨F, rfl, rfl, rfl, fun _ _ _ => rfl⟩
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Scalar drift and delay facts for the native buffer, uniformly in the
finite derivative request and the observation window. The radius cap is
chosen before requests or birth data and also supplies the existing rough
buffer's cap. The degenerate cases are included: zero orders, empty and singleton fibres, identity
geometry, edgeless seed and a zero-length observation window have the same scalars.
Only interior levels are used; the delay is not inferred from family data. -/

/-- One fixed molecular cap supplies all native drift orders and the
scalar two-renewal delay budget before the actual stage and datum. -/
def NativePreparationDriftStatement (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∃ cmax : ℝ, 0 < cmax ∧
    cmax ≤ Buffer.exists_molecular_uniform_constants.choose ∧
  ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cmax →
  ∃ mStar : ℕ, 2 ≤ mStar ∧
  ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
  ∀ m : ℕ, mStar ≤ m → m < M →
  ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ), IsOCStreamSeq α q Λ ζ Φ →
    let ρ := c₀ * min (ocEpsilon q Λ m) (Real.sqrt (κ m / ocA α q Λ m))
    ρ ^ 2 / κ m ≤ 2 * ocTauPP α q Λ m ∧
    ∀ (a b : ℝ) (Kmax : ℕ),
      Providers.WeakGen.Comparison.TorusDriftData (κ m) ρ a b
        (streamVel (Φ m)) Kmax

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The same native buffer supplies the entrance datum at variable copy-zero
orders. Truncation and reduction of the entrance radius only decrease its
weighted factorial norm. The map is linear and chosen before every mass;
its low trace and constant-data clause remain those of the original path.

The degenerate cases are included: empty and singleton families, zero orders, zero/constant data,
identity geometry and an edgeless seed use the same map. The entrance radius
may be zero or equal to the molecular radius. No extra stored-order cap,
second path, or new choice of a representative is required. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Down-truncate one uniform-order higher datum to the requested entrance slots. -/
def preparationBufferedSlotMap {Kbuf : ℕ} (K : ι → ℕ) (hK : ∀ i, K i ≤ Kbuf)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk Kbuf (h i))) :
    (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (K i) (h i)) :=
  (LinearMap.pi fun i => (truncateTorusHk (E := h i) (hK i)).toLinearMap.comp
    (LinearMap.proj i)).comp B

/-- The exact entrance norm used by the joint preparation of the copied family is bounded by the
same uniform-order buffer norm, with no radius-conversion loss. -/
theorem preparation_buffered_slot_bound {Kbuf : ℕ} (K : ι → ℕ)
    (hK : ∀ i, K i ≤ Kbuf)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk Kbuf (h i)))
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (f : ∀ i, TorusHk 0 (h i)) :
    Real.sqrt (∑ i, (π i)⁻¹ * torusHkNorm r (le_refl (K i))
      (preparationBufferedSlotMap K hK B f i) ^ 2) ≤
      Real.sqrt (massNormSq R π (fun i => (B f i).val)) := by
  classical
  apply Real.sqrt_le_sqrt
  unfold massNormSq
  refine Finset.sum_le_sum fun i _ => ?_
  rw [CycleJointProofs.torusHkNorm_full,
    Real.sq_sqrt (factorialNormSq_nonneg r _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hπ i).le)
  change factorialNormSq r (truncateJet (hK i) (B f i).val) ≤ _
  exact (CycleJointProofs.factorialNormSq_truncate_le (hK i) r (B f i).val).trans
    (CycleJointProofs.factorialNormSq_mono_radius hr hrR (B f i).val)

variable [∀ i, FiniteDimensional ℝ (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν c : ℝ} {Dm : ℕ}

/-- The proved native frame yields one linear variable-order datum with all
mass bounds and its exact low trace, before either weight or datum is chosen. -/
theorem native_buffered_slot_datum
    {P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 Dm}
    {OC : OCData} {m Kbuf : ℕ} {π : ι → ℝ} {weights : Set (ι → ℝ)}
    (I : PreparationNativeBufferInput (c := c) P OC m Kbuf π weights)
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Kbuf) :
    ∃ B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (K i) (h i)),
      (∀ f i, truncateTorusHk (Nat.zero_le (K i)) (B f i) =
        (I.path f).1 (Set.projIcc a b P.htime (a + ρ ^ 2 / ν)) i) ∧
      (∀ (r : ℝ), 0 ≤ r → r ≤ ρ → ∀ w ∈ weights, ∀ f,
        Real.sqrt (∑ i, (π i / w i ^ 2)⁻¹ *
          torusHkNorm r (le_refl (K i)) (B f i) ^ 2) ≤
          Real.sqrt (Buffer.bufferEnergyCost Kbuf) *
            Real.sqrt (massNormSq 1 (fun i => π i / w i ^ 2)
              (fun i => (f i).val))) ∧
      BufferedConstantTraceStatement K B := by
  classical
  obtain ⟨Bhigh, htrace, hbound, _⟩ := native_buffered_datum_of_frame I
    (nativeKernelBufferFrameProduction P OC m Kbuf π weights I)
  let B := preparationBufferedSlotMap K hK Bhigh
  have hlow (f : ∀ i, TorusHk 0 (h i)) (i : ι) :
      truncateTorusHk (Nat.zero_le (K i)) (B f i) =
        (I.path f).1 (Set.projIcc a b P.htime (a + ρ ^ 2 / ν)) i := by
    calc
      _ = truncateTorusHk (Nat.zero_le Kbuf) (Bhigh f i) := rfl
      _ = _ := htrace f i
  refine ⟨B, hlow, ?_, ?_⟩
  · intro r hr hrρ w hw f
    have hmass : ∀ i, 0 < π i / w i ^ 2 := by
      intro i
      rw [← congrFun (I.mass w hw (0 : Fin (Kbuf + 1))) i]
      exact (I.operators w hw 0).hπ i
    have h := (preparation_buffered_slot_bound K hK Bhigh
      (fun i => π i / w i ^ 2) hmass hr hrρ f).trans (hbound w hw f)
    rw [Real.sqrt_mul (Buffer.bufferEnergyCost_nonneg Kbuf)] at h
    have he : massNormSq ρ (fun i => π i / w i ^ 2) (fun i => (f i).val) =
        massNormSq 1 (fun i => π i / w i ^ 2) (fun i => (f i).val) :=
      (CycleJointProofs.massNormSq_order_zero ρ _ f).trans
        (CycleJointProofs.massNormSq_order_zero 1 _ f).symm
    exact he ▸ h
  · exact buffered_constant_trace_of_native P (OC.Φ m)
      (Velocity.streamSeq_admissible I.profile I.frequency I.stream m)
      I.path I.realizes K B (Set.projIcc a b P.htime (a + ρ ^ 2 / ν)) hlow

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
