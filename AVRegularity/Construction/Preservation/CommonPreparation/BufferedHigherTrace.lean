-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.AmbientKernelFlux
import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledEnergyTorus
public import AVRegularity.Construction.Preservation.Buffer.KernelMaterialIncrement
import AVRegularity.KernelEnergy.TorusKernelComponentSup
import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Whole-window copied evolution from genuine finite Eulerian coefficients.
Only the forward-copy pattern is used; no chart with an age comparable to
the whole observation duration is required. The Galerkin solver
and uniqueness give one linear trace before the data, after a copy
rank rescaling of the finite coefficient budget. The degenerate cases are included: H=0 is
uncoupled, empty and singleton components, D=2, zero coefficients, identity geometry and
point windows. No quantitative energy is claimed. -/

/-- Finite smooth periodic measurable forward-copy coefficients admit one
linear genuine weak evolution on the full bounded window. -/
def DescendingCopyLinearEvolutionStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (H D Kmax : ℕ) (K : ι × Fin (H + 1) → ℕ), 2 ≤ D → (∀ v, K v ≤ Kmax) →
  ∀ (ν ρ a b : ℝ) (v : ℝ → Vec 2 → Vec 2), 0 < ν → 0 < ρ → a ≤ b →
    Providers.WeakGen.Comparison.TorusDriftData ν ρ a b v Kmax →
  ∀ A : ∀ x y : ι × Fin (H + 1), (d : admissibleOrders K D x y) → ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h y.1)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h x.1)),
    (∀ x y d, coefficientSeminorm ρ (K x) a b (A x y d) ≠ ⊤) →
    (∀ x y d, Measurable (fun p : Set.Icc a b × Vec 2 => A x y d p.1 p.2)) →
    (∀ x y d t, t ∈ Set.Icc a b → ContDiff ℝ (K x : ℕ) (A x y d t)) →
    (∀ x y d t, t ∈ Set.Icc a b → IsZ2Periodic (A x y d t)) →
    (∀ x y d, x.2.val ≠ y.2.val + 1 → ∀ t ∈ Set.Icc a b, A x y d t = 0) →
  ∃ L : (∀ x : ι × Fin (H + 1), TorusHk (K x) (h x.1)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x) (h x.1)),
    ∀ f, ∃ W : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x + 1) (h x.1),
      IsCoupledWeakSolutionTorus ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) (L f) W

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The descending-copy linear evolution on the whole window. The copy-rank masses `DescMass`
put the forward-copy coefficients under the Schur condition (`desc_schur_of_bound`), so the coupled
energy estimate `coupled_energy_torus` gives a genuine weak solution (with its higher lift) for
every datum and
uniqueness on the window. Superposition and uniqueness select one linear trace before the data,
clamped outside the window. No chart certificate, smallness of the coefficients or new Galerkin
construction is used. The degenerate cases are included: `H = 0` (one copy rank: every
coefficient vanishes), empty or singleton components, zero coefficients and a point window
`a = b` are covered by the same proof. -/

section Linear
variable {κ : Type*} [Fintype κ] {h : κ → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K : κ → ℕ} {D : ℕ} {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
  {A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}

local instance DescNativeModule (k : ℕ) (i : κ) :
    Module ℝ (TorusHk k (h i)) := inferInstance
local instance DescCarrierSMul (k : ℕ) (i : κ) : SMul ℝ (TorusHk k (h i)) :=
  (DescNativeModule (h := h) k i).toDistribMulAction.toDistribSMul.toSMul
local instance DescFamilySMul (K : κ → ℕ) :
    SMul ℝ (∀ i, TorusHk (K i) (h i)) := Pi.instSMul

/-- Existence and uniqueness for every datum select one linear trace before the data, clamped
outside the window, with the genuine higher lifts. -/
theorem desc_linear_of_unique (hab : a ≤ b)
    (hex : ∀ f : ∀ i, TorusHk (K i) (h i), ∃ (u : ∀ i, ℝ → TorusHk (K i) (h i))
      (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (huniq : ∀ (f : ∀ i, TorusHk (K i) (h i)) (u u' : ∀ i, ℝ → TorusHk (K i) (h i))
      (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w →
      IsCoupledWeakSolutionTorus ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u' w' →
      ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t) :
    ∃ L : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, ℝ → TorusHk (K i) (h i)),
      ∀ f, ∃ W : ∀ i, ℝ → TorusHk (K i + 1) (h i),
        IsCoupledWeakSolutionTorus ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) (L f) W := by
  classical
  choose U W hs using hex
  have hadd (f g : ∀ i, TorusHk (K i) (h i)) :
      ∀ i, ∀ t ∈ Set.Icc a b, U (f + g) i t = U f i t + U g i t := by
    have hr := CycleJointProofs.PathReduction.torusWeakSolution_add (hs f) (hs g)
    simp only [add_zero] at hr
    exact huniq (f + g) _ _ _ _ (hs (f + g)) hr
  have hsmul (c : ℝ) (f : ∀ i, TorusHk (K i) (h i)) :
      ∀ i, ∀ t ∈ Set.Icc a b, U (c • f) i t = c • U f i t := by
    have hr := preparation_plain_solution_smul c (hs f)
    simp only [smul_zero] at hr
    exact huniq (fun i => c • f i) (U (c • f)) (fun i t => c • U f i t)
      (W (c • f)) (fun i t => c • W f i t) (hs (c • f)) hr
  let L : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, ℝ → TorusHk (K i) (h i)) :=
    { toFun := fun f i t => U f i (Set.projIcc a b hab t)
      map_add' := fun f g => by
        funext i t
        exact hadd f g i _ (Set.projIcc a b hab t).property
      map_smul' := fun c f => by
        funext i t
        exact hsmul c f i _ (Set.projIcc a b hab t).property }
  refine ⟨L, fun f => ⟨W f, ?_⟩⟩
  apply preparation_plain_solution_trace_congr hab (hs f)
  intro i t ht
  change U f i (Set.projIcc a b hab t) = U f i t
  rw [Set.projIcc_of_mem hab ht]

end Linear

/-- **The descending-copy linear evolution.** -/
theorem descendingCopyLinearEvolution : DescendingCopyLinearEvolutionStatement := by
  intro ι _ _ h _ _ _ _ _ _ H D Kmax K hD hK ν ρ a b v hν hρ hab hv A hAfin hAmeas hAsmooth hAper
    hfw
  let r : ι × Fin (H + 1) → ℕ := fun x => x.2.val
  have hC : 0 ≤ ∑ x, ∑ y, DescEntry ν ρ K D a b A x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => DescEntry_nonneg hν hρ x y
  let π := DescMass ((8 * ∑ x, ∑ y, DescEntry ν ρ K D a b A x y + 1) ^ 2) r
  have hπ : ∀ x, 0 < π x := DescMass_pos (pow_pos (by linarith) 2) r
  have hschur : SchurCondition (schurMatrix ν ρ π K D a b A) :=
    desc_schur hν hρ r (fun x y d hxy t ht => hfw x y d hxy t ht)
  obtain ⟨a', B₀, lam, ha, hB₀, hlam, hjets, hB, hab'⟩ := hv.jets
  have hgate := fun f : (∀ x : ι × Fin (H + 1), TorusHk (K x) (h x.1)) =>
    coupled_energy_torus a b hab ρ hρ ν hν v hv.bdd hv.meas hv.smooth hv.div hv.per
      a' B₀ lam ha hB₀ hlam Kmax hjets hB hab' D hD π hπ K hK A hAmeas
      (fun x y d t ht => hAsmooth x y d t ht) (fun x y d t ht => hAper x y d t ht) hAfin hschur
      f (fun _ _ => 0) (fun _ => timeMemLp_zero _ 2) (fun _ _ => 0)
      (fun _ => timeIntegrable_zero _)
  exact desc_linear_of_unique hab (fun f => (hgate f).1) (fun f => (hgate f).2.1)

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Linear rough kernel evolution in abstract Hilbert fibres. The uniqueness
proof is the order-zero specialization of NativeKernelSolutionUnique; keeping
it generic avoids repeating the dependent native-system instance chain.

The degenerate cases are included: empty and singleton families, zero data, order zero, identity
fibre maps, edgeless families and zero-length intervals. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {D : ℕ}
  (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

/-- Uniqueness at order zero has no positive-order drift request. -/
theorem preparation_kernel_order_zero_unique {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (f : ∀ i, TorusHk 0 (h i))
    (u u' : ∀ i, ℝ → TorusHk 0 (h i)) (w w' : ∀ i, ℝ → TorusHk 1 (h i))
    (y y' : ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α))
    (hs : IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D P.B P.C P.S f 0 0 u w y)
    (hs' : IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D P.B P.C P.S f 0 0 u' w' y') :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t := by
  classical
  obtain ⟨hv, hp, hd, ⟨V, hV⟩, hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hbV : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ max V 0 :=
    fun t ht x => (hV t ht x).trans (le_max_left _ _)
  have hforced := P.kernelWeakSolution_forcedWeakSolution (streamVel φ) hv
    (max V 0) hV0 hbV f 0 0 u w y hs
  have hforced' := P.kernelWeakSolution_forcedWeakSolution (streamVel φ) hv
    (max V 0) hV0 hbV f 0 0 u' w' y' hs'
  have hsmall : 1 * ρ / (2 * ρ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) P.radius_pos)).mpr
    ring_nf
    exact le_rfl
  have hstrain : 0 * 1 * ρ ^ 2 ≤ ν / 8 := by
    simp only [zero_mul]
    exact div_nonneg P.diffusivity_pos.le (by norm_num)
  have hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ 0 → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        0 * 1 ^ l * (l.factorial : ℝ) * (2 * ρ) ^ ((1 : ℤ) - l) := by
    intro _ _ l hl hl0
    omega
  apply P.kernelForcedWeakSolution_unique (streamVel φ) hv hp 0 0 0 1 (2 * ρ)
    le_rfl le_rfl (mul_pos (by norm_num) P.radius_pos) hsmall hstrain hd hjets hm
    (max V 0) hV0 hbV (fun _ => driftCarrierBudget 0 (max V 0) 0 1 (2 * ρ))
    (fun t ht _ => driftCarrierBudget_bounds 0 (streamVel φ t) (max V 0) 0 1 (2 * ρ)
      hV0 (hbV t ht) (hjets t ht)) w w' u u' f
    (fun _ => timeMemLp_zero _ 2) (fun _ => timeIntegrable_zero _)
  · exact hforced
  · exact hforced'

/-- Actual native trajectories for every datum, before imposing linearity. -/
structure PreparationKernelEvolution
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) where
  value : (∀ i, TorusHk 0 (h i)) → ∀ i, ℝ → TorusHk 0 (h i)
  gradient : (∀ i, TorusHk 0 (h i)) → ∀ i, ℝ → TorusHk 1 (h i)
  regularized : (∀ i, TorusHk 0 (h i)) →
    ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α)
  solution : ∀ f, IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D
    P.B P.C P.S f 0 0 (value f) (gradient f) (regularized f)

/-- Choose only the already constructed rough native solutions. -/
def preparationKernelEvolution {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) : PreparationKernelEvolution P φ := by
  classical
  choose U W Y hs using fun f : ∀ i, TorusHk 0 (h i) =>
    Buffer.TorusKernelOperator.stream_kernel_order_zero_exists P hφ f
  exact ⟨U, W, Y, hs⟩

/-- Native uniqueness identifies the sum of two chosen trajectories. -/
theorem preparation_kernel_evolution_add {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (T : PreparationKernelEvolution P φ)
    (f g : ∀ i, TorusHk 0 (h i)) : ∀ i, ∀ t ∈ Set.Icc a b,
      T.value (f + g) i t = T.value f i t + T.value g i t := by
  have hr := preparation_kernel_solution_add P (streamVel φ) f g 0 0 0 0
    (T.value f) (T.value g) (T.gradient f) (T.gradient g)
    (T.regularized f) (T.regularized g) (T.solution f) (T.solution g)
  simp only [add_zero] at hr
  exact preparation_kernel_order_zero_unique P hφ (f + g)
    (T.value (f + g)) (T.value f + T.value g) (T.gradient (f + g))
    (T.gradient f + T.gradient g) (T.regularized (f + g))
    (T.regularized f + T.regularized g) (T.solution (f + g)) hr

/-- Native uniqueness identifies every real multiple of a chosen trajectory. -/
theorem preparation_kernel_evolution_smul {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (T : PreparationKernelEvolution P φ)
    (c : ℝ) (f : ∀ i, TorusHk 0 (h i)) : ∀ i, ∀ t ∈ Set.Icc a b,
      T.value (fun i => c • f i) i t = c • T.value f i t := by
  have hr := preparation_kernel_solution_smul P (streamVel φ) f 0 0
    (T.value f) (T.gradient f) (T.regularized f) c (T.solution f)
  simp only [Pi.zero_apply, smul_zero] at hr
  exact preparation_kernel_order_zero_unique P hφ (fun i => c • f i)
    (T.value (fun i => c • f i)) (fun i t => c • T.value f i t)
    (T.gradient (fun i => c • f i)) (fun i t => c • T.gradient f i t)
    (T.regularized (fun i => c • f i)) (fun i j α t => c • T.regularized f i j α t)
    (T.solution (fun i => c • f i)) hr

/-- One linear native time trace, chosen before every initial datum. -/
theorem preparation_kernel_linear_evolution {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) :
    ∃ L : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, ℝ → TorusHk 0 (h i)),
      ∀ f, ∃ (w : ∀ i, ℝ → TorusHk 1 (h i))
        (y : ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α)),
        IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D P.B P.C P.S f 0 0 (L f) w y := by
  let T := preparationKernelEvolution P hφ
  let L : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, ℝ → TorusHk 0 (h i)) :=
    { toFun := fun f i t => T.value f i (Set.projIcc a b P.htime t)
      map_add' := fun f g => by
        funext i t
        exact preparation_kernel_evolution_add P hφ T f g i _
          (Set.projIcc a b P.htime t).property
      map_smul' := fun c f => by
        funext i t
        exact preparation_kernel_evolution_smul P hφ T c f i _
          (Set.projIcc a b P.htime t).property }
  refine ⟨L, fun f => ⟨T.gradient f, T.regularized f, ?_⟩⟩
  apply preparation_kernel_solution_trace_congr P (streamVel φ) f 0 0 (T.value f) (L f)
    (T.gradient f) (T.regularized f) (T.solution f)
  intro i t ht
  change T.value f i (Set.projIcc a b P.htime t) = T.value f i t
  rw [Set.projIcc_of_mem P.htime ht]

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Price a finite family of genuine scalar forced rows with one application of
the coupled energy estimate `coupled_energy_torus`. Its trace norm is the family mass at each time,
so no sum of component trace suprema is introduced.

Empty or singleton families, zero forcing or datum, and zero-length windows have the same
statement. Forcing carriers
exist at every time, and their time L2 hypotheses are retained. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- Whole-family forced scalar energy, with the flux parenthesization. -/
theorem preparation_scalar_family_energy {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {Kmax k : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {f : ∀ i, TorusHk k (h i)}
    {F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    {u : ∀ i, ℝ → TorusHk k (h i)} {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    (hs : ∀ i, IsTorusForcedRow ν a b v 2 k (f i) (F i) (fun _ => 0) (u i) (w i))
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    massNormSq ρ π (fun i => (u i t).val) +
      ν / 2 * (∫ s in Set.Icc a b, massGradNormSq ρ π (fun i => (w i s).val)) ≤
      2 * massNormSq ρ π (fun i => (f i).val) +
        8 / ν * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) := by
  have hsol : IsCoupledWeakSolutionTorus ν a b v 2 (fun _ => k)
      (fun _ _ _ _ _ => 0) f F (fun _ _ => 0) u w := by
    refine ⟨fun i => (hs i).1 0, fun i => (hs i).2.1 0,
      fun i => (hs i).2.2.1 0, fun i => (hs i).2.2.2.1 0, ?_⟩
    intro i r hr φ
    have he := (hs i).2.2.2.2 0 r hr φ
    simpa only [zero_apply, Finset.sum_const_zero] using he
  obtain ⟨a', B₀, lam, ha, hB₀, hlam, hjets, hB, hab'⟩ := hd.jets
  have hgate := coupled_energy_torus a b hab ρ hρ ν hν v hd.bdd hd.meas hd.smooth hd.div hd.per
    a' B₀ lam ha hB₀ hlam Kmax hjets hB hab' 2 (by decide) (ι := ι) (h := h)
    π hπ (fun _ => k) (fun _ => hk) (fun _ _ _ _ _ => 0)
    (fun _ _ _ => measurable_const) (fun _ _ _ _ _ => contDiff_const)
    (fun _ _ _ _ _ => fun _ _ => rfl)
    (fun _ _ _ => by rw [CycleComparison.Coarse.coefficientSeminorm_const_zero]; exact ENNReal.zero_ne_top)
    (CycleComparison.Coarse.zeroCoupling_schur ν ρ π _ 2 a b)
    f F hF (fun _ _ => 0) (fun i => timeIntegrable_zero (E := TorusHk k (h i)) _)
  have he := hgate.2.2 u w hsol t ht
  simpa only [torusMassNormSq_zero (fun _ => k) ρ π hπ, Real.sqrt_zero,
    integral_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using he

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual kernel equation is the sum of scalar initial-data evolution
and scalar zero-data evolution driven by its actual kernel flux. This is the
semantic fixed-point ingredient; its linear energy-path realization is separate.

The degenerate cases are included: empty and singleton families, zero datum/flux, identity geometry,
k=0, edgeless seeds and zero-length intervals preserve the full initial trace. -/

attribute [local instance] preparationScalarFluxModule preparationScalarFluxSMul
  preparationResponseNativeNormed preparationResponseNativeModule
  preparationResponseDatumAdd preparationResponseDatumMonoid preparationResponseDatumModule
local instance preparationRestartFluxAdd {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (k : ℕ) (a b : ℝ) :
    AddCommGroup (preparationScalarFluxSpace E k a b) :=
  Submodule.addCommGroup (preparationScalarFluxSpace E k a b)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {k D : ℕ}

private theorem preparation_decoupled_forced_row {v : ℝ → Vec 2 → Vec 2}
    {f : ∀ i, TorusHk k (h i)}
    {F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → TorusHk k (h i)} {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    (hs : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k)
      KernelEnergy.TorusKernelOperator.noLocalCoefficient f F g u w) (i : ι) :
    IsTorusForcedRow ν a b v 2 k (f i) (F i) (g i) (u i) (w i) := by
  refine ⟨fun _ => hs.1 i, fun _ => hs.2.1 i, fun _ => hs.2.2.1 i,
    fun _ => hs.2.2.2.1 i, ?_⟩
  intro _ t ht φ
  have he := hs.2.2.2.2 i t ht φ
  change CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v
    ((u i t).toFunction.jet (valueIndex2 k)) ((f i).toFunction.jet (valueIndex2 k))
    (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun s q => (w i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (fun s => torusRawCouplingFlux (fun _ => k) 0 s KernelEnergy.TorusKernelOperator.noLocalCoefficient
      (fun j => w j s) i)
    (fun s => (F i s).toFunction.jet (valueIndex2 k))
    (fun s => (g i s).toFunction.jet (valueIndex2 k)) at he
  have hz : (fun s => torusRawCouplingFlux (fun _ => k) 0 s
      KernelEnergy.TorusKernelOperator.noLocalCoefficient (fun j => w j s) i) =
      (fun _ _ => 0) := by
    funext s x
    exact KernelEnergy.TorusKernelOperator.noLocalRawFlux_zero w i s x
  rw [hz] at he
  simpa only [zero_apply, Finset.sum_const_zero] using he

/-- A native kernel solution solves each actual scalar forced row. -/
theorem preparation_kernel_scalar_row
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
    {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    {f : ∀ i, TorusHk k (h i)} {u : ∀ i, ℝ → TorusHk k (h i)}
    {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    {y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)}
    (hs : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f 0 0 u w y) (i : ι) :
    IsTorusForcedRow ν a b v 2 k (f i) (P.carrierFlux w i) (fun _ => 0) (u i) (w i) := by
  obtain ⟨C, hC⟩ := hd.bdd
  have hbound : ∀ s ∈ Set.Icc a b, ∀ x, ‖v s x‖ ≤ max C 0 :=
    fun s hs x => (hC s hs x).trans (le_max_left _ _)
  have hforced := P.kernelWeakSolution_forcedWeakSolution v hd.smooth (max C 0)
    (le_max_right _ _) hbound f 0 0 u w y hs
  simp only [Pi.zero_apply, zero_add] at hforced
  exact preparation_decoupled_forced_row hforced i

/-- A homogeneous row plus a zero-initial forced row reconstructs the row
with their common full initial datum and the time-equivalent forcing. -/
theorem preparation_scalar_zero_source_split {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    {f : TorusHk k E}
    {F Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))}
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b)))
    (hQ : Q =ᵐ[volume.restrict (Set.Icc a b)] F)
    {u u₀ uk : ℝ → TorusHk k E} {w w₀ wk : ℝ → TorusHk (k + 1) E}
    (hs : IsTorusForcedRow ν a b v 2 k f F (fun _ => 0) u w)
    (hs₀ : IsTorusForcedRow ν a b v 2 k f (fun _ => 0) (fun _ => 0) u₀ w₀)
    (hsk : IsTorusForcedRow ν a b v 2 k 0 Q (fun _ => 0) uk wk) :
    ∀ t ∈ Set.Icc a b, u t = u₀ t + uk t := by
  have ha := CycleJointProofs.PathReduction.torusWeakSolution_add hs₀ hsk
  simp only [add_zero, zero_add] at ha
  have hc := CycleJointProofs.PathReduction.torusRowSolution_forcing_congr ν a b v 2 k f Q F
    (fun t => u₀ t + uk t) (fun t => w₀ t + wk t) hQ ha
  exact torusForcedRow_unique hd hab hρ hν le_rfl hk hF
    (CoupledEnergy.Variational.timeIntegrable_zero _) hs hc

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Actual native solutions determine one linear continuous-trace/ambient-L2
energy path. The trace covers the whole solution window; only the higher
readout is restricted to the post-buffer window. No independent solution is
chosen for the two weights.

The degenerate cases are included: empty and singleton families, zero datum, identity geometry,
order zero, edgeless seeds and zero-length windows. The buffer
endpoint is no earlier than the initial time; an empty higher-class window
is allowed and all initial values are retained. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {D : ℕ}

local instance preparationNativeFamilyNormed (k : ℕ) :
    NormedAddCommGroup (∀ i, TorusHk k (h i)) := inferInstance
local instance preparationNativeFamilyModule (k : ℕ) :
    Module ℝ (∀ i, TorusHk k (h i)) := Pi.module _ _ _
local instance preparationNativeContinuousModule (a b : ℝ) :
    Module ℝ C(Set.Icc a b, ∀ i, TorusHk 0 (h i)) := ContinuousMap.module

/-- Synthesis from genuine higher carriers to the ambient higher jet family. -/
def preparationNativeHigherJetsCLM :
    (∀ i, TorusHk 1 (h i)) →L[ℝ] CoupledHighHilbert (h := h) (fun _ => 0) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun i => JetL2 (volume.restrict unitCube) 1 (h i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (torusHkGraph (E := h i) 1).toSubmodule.subtypeL.comp (ContinuousLinearMap.proj i)))

/-- The actual equation and higher class realized by a native path map. -/
def NativeEnergyPathRealizes
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (c : ℝ)
    (L : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) : Prop :=
    ∀ f, ∃ (w : ∀ i, ℝ → TorusHk 1 (h i))
      (y : ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α)),
      IsKernelWeakSolutionTorus ν a b (streamVel φ) 0 D P.B P.C P.S f 0 0
        (fun i t => (L f).1 (Set.projIcc a b P.htime t) i) w y ∧
      ((L f).2 =ᵐ[volume.restrict (Set.Icc c b)]
        fun t => coupledCarrierHighJets (fun _ => 0) (fun i => w i t))

/-- One actual linear native evolution with its actual higher ambient class. -/
def NativeEnergyPathStatement
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    (φ : ℝ → Vec 2 → ℝ) (c : ℝ) : Prop :=
  ∃ L : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b c,
    NativeEnergyPathRealizes P φ c L

omit [Fintype ι] in
private theorem preparation_family_truncate_injective :
    Function.Injective (fun w : ∀ i, TorusHk 1 (h i) =>
      fun i => truncateTorusHk (Nat.zero_le 1) (w i)) := by
  intro w z he
  funext i
  apply TorusHk.ext_value
  exact congrArg (fun f : TorusHk 0 (h i) => f.val (valueIndex2 0)) (congrFun he i)

/-- Restrict a linear family trace to its continuous whole-window path. -/
def preparation_native_continuous_trace {X : Type*} [AddCommGroup X] [Module ℝ X]
    (L : X →ₗ[ℝ] (∀ i, ℝ → TorusHk 0 (h i)))
    (hc : ∀ f i, ContinuousOn (L f i) (Set.Icc a b)) :
    X →ₗ[ℝ] C(Set.Icc a b, ∀ i, TorusHk 0 (h i)) :=
  { toFun := fun f => ⟨fun t i => L f i t,
      continuous_pi (fun i => (hc f i).domRestrict)⟩
    map_add' := fun f g => by
      apply ContinuousMap.ext
      intro t
      funext i
      exact congrFun (congrFun (L.map_add' f g) i) t
    map_smul' := fun r f => by
      apply ContinuousMap.ext
      intro t
      funext i
      exact congrFun (congrFun (L.map_smul' r f) i) t }

/-- Genuine higher lifts of a linear trace determine one ambient higher L2 map. -/
theorem preparation_native_higher_time_class {X : Type*}
    [AddCommGroup X] [Module ℝ X] (c b : ℝ)
    (L : X →ₗ[ℝ] (∀ i, ℝ → TorusHk 0 (h i)))
    (W : X → ∀ i, ℝ → TorusHk 1 (h i))
    (hm : ∀ f i, MemLp (W f i) 2 (volume.restrict (Set.Icc c b)))
    (ha : ∀ f i, ∀ᵐ t ∂volume.restrict (Set.Icc c b),
      truncateTorusHk (Nat.zero_le 1) (W f i t) = L f i t) :
    ∃ B : X →ₗ[ℝ] CoupledHighTime (h := h) (fun _ => 0) c b,
      ∀ f, B f =ᵐ[volume.restrict (Set.Icc c b)]
        fun t => coupledCarrierHighJets (fun _ => 0) (fun i => W f i t) := by
  let Ltime : X →ₗ[ℝ] (ℝ → ∀ i, TorusHk 0 (h i)) :=
    { toFun := fun f t i => L f i t
      map_add' := fun f g => by
        funext t i
        exact congrFun (congrFun (L.map_add' f g) i) t
      map_smul' := fun r f => by
        funext t i
        exact congrFun (congrFun (L.map_smul' r f) i) t }
  let T : (∀ i, TorusHk 1 (h i)) →ₗ[ℝ] (∀ i, TorusHk 0 (h i)) :=
    LinearMap.pi (fun i => (truncateTorusHk (E := h i) (Nat.zero_le 1)).toLinearMap.comp
      (LinearMap.proj i))
  have hT : Function.Injective T := preparation_family_truncate_injective
  have ha' : ∀ f, ∀ᵐ t ∂volume.restrict (Set.Icc c b),
      T (fun i => W f i t) = Ltime f t := by
    intro f
    filter_upwards [ae_all_iff.mpr (ha f)] with t ht
    exact funext ht
  let A := preparationNativeHigherJetsCLM (h := h)
  let Q := fun f t => A (fun i => W f i t)
  have hm' : ∀ f, MemLp (Q f) 2 (volume.restrict (Set.Icc c b)) :=
    fun f => coupledCarrierHighJets_memLp (fun _ => 0) c b (W f) (hm f)
  have hadd : ∀ f g, Q (f + g) =ᵐ[volume.restrict (Set.Icc c b)] fun t => Q f t + Q g t := by
    intro f g
    have hh := preparation_time_lift_add _ Ltime T hT (fun f t i => W f i t) ha' f g
    filter_upwards [hh] with t ht
    change A (fun i => W (f + g) i t) = A (fun i => W f i t) + A (fun i => W g i t)
    exact (congrArg A ht).trans (A.map_add _ _)
  have hsmul : ∀ (r : ℝ) f, Q (r • f) =ᵐ[volume.restrict (Set.Icc c b)] fun t => r • Q f t := by
    intro r f
    have hh := preparation_time_lift_smul _ Ltime T hT (fun f t i => W f i t) ha' r f
    filter_upwards [hh] with t ht
    change A (fun i => W (r • f) i t) = r • A (fun i => W f i t)
    exact (congrArg A ht).trans (A.map_smul r _)
  obtain ⟨B, hB⟩ := preparation_time_class_linear _ Q hm' hadd hsmul
  refine ⟨B, fun f => ?_⟩
  rw [hB f]
  exact (hm' f).coeFn_toLp

/-- Equality of actual low traces determines addition of their ambient higher classes. -/
theorem preparation_native_higher_add_of_traces (c b : ℝ)
    (U V Z : CoupledHighTime (h := h) (fun _ => 0) c b)
    (W W₀ Wk : ∀ i, ℝ → TorusHk 1 (h i))
    (hW : U =ᵐ[volume.restrict (Set.Icc c b)]
      fun t => coupledCarrierHighJets (fun _ => 0) (fun i => W i t))
    (hW₀ : V =ᵐ[volume.restrict (Set.Icc c b)]
      fun t => coupledCarrierHighJets (fun _ => 0) (fun i => W₀ i t))
    (hWk : Z =ᵐ[volume.restrict (Set.Icc c b)]
      fun t => coupledCarrierHighJets (fun _ => 0) (fun i => Wk i t))
    (htr : ∀ᵐ t ∂volume.restrict (Set.Icc c b), ∀ i,
      truncateTorusHk (Nat.zero_le 1) (W i t) =
        truncateTorusHk (Nat.zero_le 1) (W₀ i t) +
          truncateTorusHk (Nat.zero_le 1) (Wk i t)) : U = V + Z := by
  apply Lp.ext
  filter_upwards [hW, hW₀, hWk, Lp.coeFn_add V Z, htr]
    with t hwt hw₀t hwkt hadd ht
  rw [hwt, hadd, Pi.add_apply, hw₀t, hwkt]
  let A := preparationNativeHigherJetsCLM (h := h)
  change A (fun i => W i t) = A (fun i => W₀ i t) + A (fun i => Wk i t)
  have he : (fun i => W i t) = (fun i => W₀ i t) + (fun i => Wk i t) := by
    funext i
    apply TorusHk.ext_value
    exact congrArg (fun z : TorusHk 0 (h i) => z.val (valueIndex2 0)) (ht i)
  exact (congrArg A he).trans (A.map_add _ _)

/-- Restart an actual native path at the buffer without changing its full
buffer datum or its ambient higher class. -/
theorem native_energy_path_restart
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    {φ : ℝ → Vec 2 → ℝ} {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (F : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (hF : NativeEnergyPathRealizes P φ c F) (f : ∀ i, TorusHk 0 (h i)) :
    ∃ (w : ∀ i, ℝ → TorusHk 1 (h i))
      (y : ∀ i j (α : Γ i j), ℝ → TorusHk (0 + D - 1) (G i j α)),
      IsKernelWeakSolutionTorus ν c b (streamVel φ) 0 D P.B P.C P.S
        ((F f).1 ⟨c, hac, hcb⟩) 0 0
        (fun i t => (F f).1 (Set.projIcc a b P.htime t) i) w y ∧
      ((F f).2 =ᵐ[volume.restrict (Set.Icc c b)]
        fun t => coupledCarrierHighJets (fun _ => 0) (fun i => w i t)) := by
  obtain ⟨W, Y, hs, hW⟩ := hF f
  let u := fun i t => (F f).1 (Set.projIcc a b P.htime t) i
  have hr := P.kernelWeakSolution_restart (streamVel φ) f 0 0 u W Y hs c ⟨hac, hcb⟩
  have hi : (fun i => u i c) = (F f).1 ⟨c, hac, hcb⟩ := by
    funext i
    change (F f).1 (Set.projIcc a b P.htime c) i = _
    rw [Set.projIcc_of_mem P.htime ⟨hac, hcb⟩]
  rw [hi] at hr
  exact ⟨W, Y, hr, hW⟩

/-- Continuous native traces and their higher classes are linear before the datum. -/
theorem native_energy_path_of_operator
    (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {c : ℝ}
    (hac : a ≤ c) : NativeEnergyPathStatement P φ c := by
  classical
  obtain ⟨L, hL⟩ := preparation_kernel_linear_evolution P hφ
  choose W Y hs using hL
  let U := preparation_native_continuous_trace L (fun f i => (hs f).1 i)
  have hμ : volume.restrict (Set.Icc c b) ≤ volume.restrict (Set.Icc a b) :=
    Measure.restrict_mono (Set.Icc_subset_Icc hac le_rfl) le_rfl
  obtain ⟨B, hB⟩ := preparation_native_higher_time_class c b L W
    (fun f i => ((hs f).2.1 i).mono_measure hμ)
    (fun f i => ((hs f).2.2.1 i).filter_mono (ae_mono hμ))
  refine ⟨U.prod B, fun f => ⟨W f, Y f, ?_, hB f⟩⟩
  apply preparation_kernel_solution_trace_congr P (streamVel φ) f 0 0 (L f)
    (fun i t => (U.prod B f).1 (Set.projIcc a b P.htime t) i) (W f) (Y f) (hs f)
  intro i t ht
  change L f i (Set.projIcc a b P.htime t) = L f i t
  rw [Set.projIcc_of_mem P.htime ht]

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The high buffered datum is one linear map, chosen before the masses.
The analytic input is pointwise higher regularity of the actual low trace,
supplied by NativeWeightedBufferAfterDelay. Mathlib's restriction to an
injective linear range selects the higher trace. Its uniqueness transfers
ANY later bound on a representative to this same map.

The degenerate cases are included: order zero, empty and singleton families, zero data and
constants, trivial fibres, identity geometry and edgeless seeds require no division by a norm.
No preparation
pair or quiet time is assumed; the caller supplies the scalar buffer time.
This is a selection adapter, not a new smoothing estimate. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- The actual low trace has its genuine higher Sobolev value at every datum. -/
def HigherTraceRepresentativesStatement (K : ℕ)
    (L : X →ₗ[ℝ] (∀ i, TorusHk 0 (h i))) : Prop :=
  ∀ f, ∃ u : ∀ i, TorusHk K (h i),
    ∀ i, truncateTorusHk (Nat.zero_le K) (u i) = L f i

/-- One linear higher trace precedes all weighted bounds. A bound supplied
for any same-value representative transfers to this very map. -/
def HigherBufferedTraceMapStatement (K : ℕ)
    (L : X →ₗ[ℝ] (∀ i, TorusHk 0 (h i))) : Prop :=
  ∃ B : X →ₗ[ℝ] (∀ i, TorusHk K (h i)),
    (∀ f i, truncateTorusHk (Nat.zero_le K) (B f i) = L f i) ∧
    ∀ (p : (∀ i, TorusHk K (h i)) → ℝ) (N : X → ℝ) (C : ℝ),
      (∀ f, ∃ u : ∀ i, TorusHk K (h i),
        (∀ i, truncateTorusHk (Nat.zero_le K) (u i) = L f i) ∧ p u ≤ C * N f) →
      ∀ f, p (B f) ≤ C * N f

/-- The already proved pointwise buffer regularity selects a linear datum
without a second evolution or a mass-dependent representative. -/
theorem higher_buffered_trace_map_of_representatives (K : ℕ)
    (L : X →ₗ[ℝ] (∀ i, TorusHk 0 (h i)))
    (hrep : HigherTraceRepresentativesStatement K L) :
    HigherBufferedTraceMapStatement K L := by
  let T : (∀ i, TorusHk K (h i)) →ₗ[ℝ] (∀ i, TorusHk 0 (h i)) :=
    LinearMap.pi fun i => (truncateTorusHk (E := h i) (Nat.zero_le K)).toLinearMap.comp
      (LinearMap.proj i)
  have hT : Function.Injective T := by
    intro u v huv
    funext i
    apply TorusHk.ext_value
    exact congrArg (fun z : TorusHk 0 (h i) => z.val (valueIndex2 0)) (congrFun huv i)
  have hRange : ∀ f, L f ∈ T.range := by
    intro f
    obtain ⟨u, hu⟩ := hrep f
    exact ⟨u, funext hu⟩
  let B := LinearMap.codRestrictOfInjective L T hT hRange
  have hB (f : X) : T (B f) = L f :=
    LinearMap.codRestrictOfInjective_comp_apply L T hT hRange f
  refine ⟨B, fun f i => congrFun (hB f) i, ?_⟩
  intro p N C hbound f
  obtain ⟨u, hu, hp⟩ := hbound f
  have he : B f = u := hT ((hB f).trans (funext hu).symm)
  exact he.symm ▸ hp

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
