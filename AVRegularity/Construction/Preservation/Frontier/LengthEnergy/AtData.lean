-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.CycleComparison.Error.Main
public import AVRegularity.KernelEnergy.TorusKernelFiniteTraceLimit
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.Proofs.WeakGen.Comparison.GateInputs
public import AVRegularity.Construction.Preservation.Frontier.GradeRows.Producer
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.Construction.Preservation.Frontier.LengthPrice.Producer
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier.LengthEnergy

/-! Principal component restriction of a kernel system. Its external forcing is exactly
the flux from the excluded columns; all spatial integrability clauses transfer at every time. -/

section
open KernelEnergy
open scoped Classical
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {k D : ℕ}

/-- A nonnegative sum decreases on an injectively labelled component block. -/
theorem length_block_embedding_sum_le {κ : Type*} [Fintype κ] (e : κ ↪ ι)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) : (∑ i : κ, f (e i)) ≤ ∑ i, f i := by
  apply Finset.sum_le_sum_of_injOn e
  · intro i _ j _ hij
    exact e.injective hij
  · intro i _
    exact Finset.mem_univ _
  · intro i _
    exact le_rfl
  · intro i _ _
    exact hf i

/-- Injective relabelling of a principal finite component block preserves its operator constants.
The degenerate cases are included: empty and singleton blocks and the full block require no changed
smallness threshold. -/
def reindexKernelComponents {κ : Type*} [Fintype κ]
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) (e : κ ↪ ι) :
    TorusKernelOperator (h := fun i : κ => h (e i))
      (Γ := fun i j => Γ (e i) (e j)) (G := fun i j α => G (e i) (e j) α) a b ρ ν k D := by
  let A := kernelSchurMatrix ν ρ P.π k D a b P.c P.r P.C P.B
  have hA (i j : ι) : 0 ≤ A i j := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply Finset.sum_nonneg
    intro α _
    apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg
    intro d _
    exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg
      ((P.hS i j α).2.2.1 _ (by have := Finset.mem_Icc.mp d.2; omega)))
      (mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr i j α).le _))
  exact {
    htime := P.htime
    radius_pos := P.radius_pos
    diffusivity_pos := P.diffusivity_pos
    order_ge_two := P.order_ge_two
    π := fun i => P.π (e i)
    hπ := fun i => P.hπ (e i)
    B := fun i j => P.B (e i) (e j)
    hB_meas := fun i j => P.hB_meas (e i) (e j)
    hB_smooth := fun i j => P.hB_smooth (e i) (e j)
    hB_per := fun i j => P.hB_per (e i) (e j)
    hB_fin := fun i j => P.hB_fin (e i) (e j)
    C := fun i j => P.C (e i) (e j)
    S := fun i j => P.S (e i) (e j)
    c := P.c
    r := fun i j => P.r (e i) (e j)
    hr := fun i j => P.hr (e i) (e j)
    hS := fun i j => P.hS (e i) (e j)
    θ := P.θ
    hθ := P.hθ
    hschur := ⟨fun i => (length_block_embedding_sum_le e (A (e i)) (hA (e i))).trans (P.hschur.1 (e i)),
      fun j => (length_block_embedding_sum_le e (fun i => A i (e j)) (fun i => hA i (e j))).trans
        (P.hschur.2 (e j))⟩ }

/-- Restriction to a component predicate, with every operator constant preserved. -/
def restrictKernelComponents
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) (sel : ι → Prop) :
    TorusKernelOperator (h := fun i : {i // sel i} => h i.1)
      (Γ := fun i j => Γ i.1 j.1) (G := fun i j α => G i.1 j.1 α) a b ρ ν k D :=
  reindexKernelComponents P ⟨Subtype.val, Subtype.val_injective⟩

/-- The excluded columns' literal supplied kernel flux into a selected row. -/
def crossingKernelFlux
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) (sel : ι → Prop)
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (i : {i // sel i}) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.1) :=
  ∑ j : {j // ¬sel j}, ∑ α : Γ i.1 j.1, ∑ d : ↥(Finset.Icc 2 D),
    P.B i.1 j.1 α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (y i.1 j.1 α t).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ x)

/-- Canonical external forcing of a component block. Equality with a supplied fresh row
will only be needed almost everywhere in time. -/
def blockCarrierForcing
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) (sel : ι → Prop)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : {i // sel i}) (t : ℝ) :
    TorusHk k (PiLp 2 (fun _ : Fin 2 => h i.1)) :=
  P.carrierFlux w i.1 t - (restrictKernelComponents P sel).carrierFlux (fun j => w j.1) i t

/-- The canonical block forcing is time-L2 without assumptions on chosen raw representatives. -/
theorem block_carrier_forcing_memLp
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) (sel : ι → Prop)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : {i // sel i}) :
    MemLp (blockCarrierForcing P sel w i) 2 (volume.restrict (Set.Icc a b)) :=
  (P.carrierFlux_memLp_of_family w hw i.1).sub
    ((restrictKernelComponents P sel).carrierFlux_memLp_of_family
      (fun j => w j.1) (fun j => hw j.1) i)

/-- Canonical carrier form of the restricted equation. The flux sum agrees in the carrier
at every time, so the every-time integrability of the weak identity `CoupledWeakIdentity` is
preserved exactly. -/
theorem block_carrier_weak_solution
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) (sel : ι → Prop)
    (v : ℝ → Vec 2 → Vec 2) (f : ∀ i, TorusHk k (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hs : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k)
      TorusKernelOperator.noLocalCoefficient f (P.carrierFlux w) (fun _ _ => 0) u w) :
    let R := restrictKernelComponents P sel
    IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k)
      TorusKernelOperator.noLocalCoefficient (fun i => f i.1)
      (fun i t => blockCarrierForcing P sel w i t + R.carrierFlux (fun j => w j.1) i t)
      (fun _ _ => 0) (fun i => u i.1) (fun i => w i.1) := by
  refine ⟨fun i => hs.1 i.1, fun i => hs.2.1 i.1, fun i => hs.2.2.1 i.1,
    fun i => hs.2.2.2.1 i.1, ?_⟩
  intro i t ht φ
  have hh := hs.2.2.2.2 i.1 t ht φ
  change CoupledWeakIdentity _ _ _ _ _ _ _ _ _ _
    (fun r x => CoupledEnergy.Variational.torusRawCouplingFlux (fun _ : ι => k) 0 r
      TorusKernelOperator.noLocalCoefficient (fun j => w j r) i.1 x) _ _ at hh
  change CoupledWeakIdentity _ _ _ _ _ _ _ _ _ _
    (fun r x => CoupledEnergy.Variational.torusRawCouplingFlux (fun _ : {i // sel i} => k) 0 r
      TorusKernelOperator.noLocalCoefficient (fun j => w j.1 r) i x) _ _
  simpa only [blockCarrierForcing, sub_add_cancel, TorusKernelOperator.noLocalRawFlux_zero]
    using hh
end

/-! The forced kernel energy estimate (`kernelForcedWeakSolution_energy`) gives the exact factor 16
for a zero-trace principal block.
This is the analytic energy step, before identifying the canonical forcing with a fresh row. -/

section
open KernelEnergy CoupledEnergy.Variational
open scoped Classical
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {k D : ℕ}

/-- A zero-trace component block dissipates at most sixteen times its canonical forcing
energy. The degenerate cases are included: empty/full selections, singleton fibres, k=0, zero
initial data and drift, identity geometry and edgeless systems require no additional premise. -/
theorem kernel_forced_block_energy
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) (sel : ι → Prop)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (α B lam : ℝ) (hα : 0 ≤ α) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ i, TorusHk k (h i)) (u : ∀ i, ℝ → TorusHk k (h i))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (hf : ∀ i, sel i → f i = 0)
    (hs : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k)
      TorusKernelOperator.noLocalCoefficient f (P.carrierFlux w) (fun _ _ => 0) u w) :
    ν * (∫ t in Set.Icc a b, massGradNormSq ρ (fun i : {i // sel i} => P.π i.1)
      (fun i => (w i.1 t).val)) ≤
        16 * ν⁻¹ * (∫ t in Set.Icc a b,
          massNormSq ρ (fun i : {i // sel i} => P.π i.1)
            (fun i => (blockCarrierForcing P sel w i t).val)) := by
  let R := restrictKernelComponents P sel
  have hsol := block_carrier_weak_solution P sel v f u w hs
  have he := R.kernelForcedWeakSolution_energy v hv hp (blockCarrierForcing P sel w)
    (fun _ _ => 0) α B lam hα hB hlam hsmall hstrain hd hjets hm V hV hvb
    (fun _ => driftCarrierBudget k V α B lam)
    (fun t ht _ => driftCarrierBudget_bounds k (v t) V α B lam hV (hvb t ht) (hjets t ht))
    (fun i => w i.1) (fun i => u i.1) (fun i => f i.1)
    (block_carrier_forcing_memLp P sel w hs.2.1)
    (fun i => integrable_zero ℝ (TorusHk k (h i.1))
      (volume.restrict (Set.Icc a b))) hsol b ⟨P.htime, le_rfl⟩
  have hz : massNormSq ρ R.π (fun i => (f i.1).val) = 0 := by
    simp only [hf _ (Subtype.property _), Submodule.coe_zero, massNormSq,
      CycleComparison.Coarse.factorialNormSq_zero_jet, mul_zero, Finset.sum_const_zero]
  have hg : massNormSq ρ R.π
      (fun i => (0 : TorusHk k (h i.1)).val) = 0 := by
    simp only [Submodule.coe_zero, massNormSq,
      CycleComparison.Coarse.factorialNormSq_zero_jet, mul_zero, Finset.sum_const_zero]
  simp only [hz, hg, Real.sqrt_zero, integral_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_add, add_zero] at he
  have hdrop := (le_add_of_nonneg_left
    (massNormSq_nonneg ρ R.π R.hπ (fun i => (u i.1 b).val))).trans he
  change ν * (∫ t in Set.Icc a b, massGradNormSq ρ R.π (fun i => (w i.1 t).val)) ≤
    16 * ν⁻¹ * (∫ t in Set.Icc a b,
      massNormSq ρ R.π (fun i => (blockCarrierForcing P sel w i t).val))
  calc
    _ = 2 * ((ν / 2) * ∫ t in Set.Icc a b,
        massGradNormSq ρ R.π (fun i => (w i.1 t).val)) := by ring
    _ ≤ 2 * ((8 / ν) * ∫ t in Set.Icc a b,
        massNormSq ρ R.π (fun i => (blockCarrierForcing P sel w i t).val)) :=
      mul_le_mul_of_nonneg_left hdrop (by norm_num)
    _ = _ := by ring
end

end AVRegularity.Construction.Preservation.Frontier.LengthEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier.LengthEnergy

/-! The remaining length-source dissipation is reduced to one forced copied-block estimate
and a finite scalar induction. The fresh-prefix rows are already produced in LengthPrice;
the PDE ingredient concerns only the contractive copied block within one length. -/

section
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Marked gradient dissipation in one word-length layer. -/
def prefixDissipation (F : Frame D hr Dm bw j₀) (l : ℕ) : ℝ :=
  D.κ (F.m - 1) * ∫ t in Set.Icc F.tp F.tf,
    massGradNormSq (E := fun v : CompIn F.Gr.comps => hr v.1.root) (K := fun _ => F.k)
      (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
      (fun v => if (compWord F.m v.1).length = l then (F.Yw v t).val else 0)

/-- The literal prefix-row realization used by the proved WordLengthRowStatement. -/
def RealizesPrefix (F : Frame D hr Dm bw j₀) (l : ℕ) (OF : F.RowFlux) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
    (OF v t).toFunction.jet (valueIndex2 F.k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => if compGrade v.1 ≤ F.H ∧ (compWord F.m v.1).length = l then
        omittedFlux F.G' F.k (IsRetained F.m F.H (l - 1)) F.yom v t x else 0

/-- ROUTINE: empty-word dissipation is bounded by the full retained contraction.
The degenerate cases are included: J=0 uses only this assertion; empty, singleton and edgeless
families, k=0, identity metric and zero datum are covered without dividing by an initial norm. -/
def EmptyWordDissipationStatement (F : Frame D hr Dm bw j₀) : Prop :=
  prefixDissipation F 0 ≤ F.initialNorm ^ 2

/-- PDE ingredient: each nonempty copied word-length block has zero initial trace
and is forced only by the fresh prefix row. The factor 16 is the forced kernel-energy
constant after dropping the terminal value square.
The degenerate cases are included: empty families and zero data give zero; J=0 asks nothing; l=1 is
forced by empty words; k=0, singleton families and identity metric require the same estimate. -/
def CopiedWordBlockEnergyStatement (F : Frame D hr Dm bw j₀) : Prop :=
  ∀ l : ℕ, 1 ≤ l → l ≤ F.J → ∀ OF : F.RowFlux,
    RealizesPrefix F l OF →
    (∀ v, MemLp (OF v) 2 (volume.restrict (Set.Icc F.tp F.tf))) →
      prefixDissipation F l ≤ 16 * F.rowEnergy OF

/-- ROUTINE scalar induction, independent of fibres, PDE solutions and Bochner integrals.
The degenerate cases are included: J=0 is the base estimate, C=0 forces all positive layers to
vanish, and I=0 needs no division. Both theta exponents may have either sign, with E strictly
positive. -/
def PrefixDissipationInductionStatement : Prop :=
  ∀ (E θ₁ θ₂ C I : ℝ) (J : ℕ) (a : ℕ → ℝ), 0 < E → a 0 ≤ I ^ 2 →
    (∀ l : ℕ, 1 ≤ l → l ≤ J →
      a l ≤ (4 * C * E ^ (if l = 1 then θ₁ else θ₂)) ^ 2 * a (l - 1)) →
    a J ≤ ((4 * C) ^ J * E ^ (if J = 0 then 0 else θ₁ + (J - 1 : ℕ) * θ₂) * I) ^ 2

/-- Exact conditional stage assembly of SourceLayerEnergyStatement in its length form.
The caller supplies the indexed rows from the proved length_rows_production; only the
copied-block energy and empty-word contraction are analytic inputs. -/
theorem length_source_energy_of_ingredients (hscalar : PrefixDissipationInductionStatement)
    (F : Frame D hr Dm bw j₀) (C : ℝ) (hE : 0 < D.eps (F.m - 1))
    (hrows : WordLengthRowsStatement F C)
    (hbase : EmptyWordDissipationStatement F) (hblock : CopiedWordBlockEnergyStatement F) :
    SourceLayerEnergyStatement F false ((4 * C) ^ F.J) := by
  have hrec (l : ℕ) (hl : 1 ≤ l) (hlJ : l ≤ F.J) :
      prefixDissipation F l ≤
        (4 * C * D.eps (F.m - 1) ^ (if l = 1 then F.θ₁ else F.θ₂)) ^ 2 *
          prefixDissipation F (l - 1) := by
    obtain ⟨OF, hOF, hLp, hprice⟩ := hrows l hl (by omega)
    have hforced := hblock l hl hlJ OF hOF hLp
    calc
      _ ≤ 16 * F.rowEnergy OF := hforced
      _ ≤ 16 * ((C * D.eps (F.m - 1) ^ (if l = 1 then F.θ₁ else F.θ₂)) ^ 2 *
          prefixDissipation F (l - 1)) :=
        mul_le_mul_of_nonneg_left hprice (by norm_num)
      _ = _ := by ring
  have hh := hscalar (D.eps (F.m - 1)) F.θ₁ F.θ₂ C F.initialNorm F.J
    (prefixDissipation F) hE hbase hrec
  simpa only [SourceLayerEnergyStatement, Frame.sourceDissipation, Bool.false_eq_true,
    Bool.false_or, Frame.layerGain, ite_false, decide_eq_true_eq, prefixDissipation] using hh
end

/-! Scalar propagation of the fresh-prefix gains, and the empty-word base supplied by
retained contraction. No estimate is assumed about nonempty copied blocks here. -/

section
open scoped Classical

private def prefixGain (E θ₁ θ₂ : ℝ) (l : ℕ) : ℝ :=
  E ^ (if l = 0 then 0 else θ₁ + (l - 1 : ℕ) * θ₂)

private theorem prefixGain_succ (E θ₁ θ₂ : ℝ) (hE : 0 < E) (l : ℕ) :
    prefixGain E θ₁ θ₂ (l + 1) =
      E ^ (if l + 1 = 1 then θ₁ else θ₂) * prefixGain E θ₁ θ₂ l := by
  cases l with
  | zero => norm_num [prefixGain]
  | succ l =>
    have hn : l + 1 + 1 ≠ 1 := by omega
    have hz : l + 1 ≠ 0 := by omega
    simp only [prefixGain, Nat.add_sub_cancel, hn, hz, Nat.add_one_ne_zero,
      ite_false, Nat.cast_add, Nat.cast_one]
    rw [← Real.rpow_add hE]
    congr 1
    ring

/-- Finite scalar induction gives precisely one theta1 gain and J-1 theta2 gains.
The degenerate cases are included: J=0 is the supplied base; zero C or initial norm causes no
division, and the positive base E permits arbitrary real exponents. -/
theorem prefix_dissipation_induction : PrefixDissipationInductionStatement := by
  intro E θ₁ θ₂ C I J a hE hbase hstep
  have hi (l : ℕ) (hl : l ≤ J) :
      a l ≤ ((4 * C) ^ l * prefixGain E θ₁ θ₂ l * I) ^ 2 := by
    induction l with
    | zero => simpa only [pow_zero, prefixGain, ite_true, Real.rpow_zero, one_mul] using hbase
    | succ l ih =>
      have hp := ih (by omega)
      have hs := hstep (l + 1) (by omega) hl
      simp only [Nat.add_sub_cancel] at hs
      calc
        a (l + 1) ≤ (4 * C * E ^ (if l + 1 = 1 then θ₁ else θ₂)) ^ 2 * a l := hs
        _ ≤ (4 * C * E ^ (if l + 1 = 1 then θ₁ else θ₂)) ^ 2 *
            ((4 * C) ^ l * prefixGain E θ₁ θ₂ l * I) ^ 2 :=
          mul_le_mul_of_nonneg_left hp (sq_nonneg _)
        _ = ((4 * C) ^ (l + 1) * prefixGain E θ₁ θ₂ (l + 1) * I) ^ 2 := by
          rw [pow_succ, prefixGain_succ E θ₁ θ₂ hE]
          ring
  exact hi J le_rfl

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Selecting the empty-word components decreases the retained gradient integral.
The degenerate cases are included: empty families and J=0 are allowed; this uses componentwise MemLp
before comparing Bochner integrals, so nonintegrability cannot manufacture a zero bound. -/
theorem empty_word_dissipation_of_contraction (F : Frame D hr Dm bw j₀)
    (hν : 0 ≤ D.κ (F.m - 1))
    (hπ : ∀ v : CompIn F.Gr.comps, 0 < F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
    (hw : ∀ v, MemLp (F.Yw v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hfull : SourceLayerEnergyStatement F true 1) : EmptyWordDissipationStatement F := by
  let W (v : CompIn F.Gr.comps) (t : ℝ) : TorusHk (F.k + 1) (hr v.1.root) :=
    if (compWord F.m v.1).length = 0 then F.Yw v t else 0
  have hW : ∀ v, MemLp (W v) 2 (volume.restrict (Set.Icc F.tp F.tf)) := by
    intro v
    by_cases hv : (compWord F.m v.1).length = 0
    · simpa only [W, ite_eq_left hv] using hw v
    · simp only [W, ite_eq_right hv]
      exact AVRegularity.Providers.WeakGen.Comparison.torusHk_memLp_zero (F.k + 1) _
  have hpoint (t : ℝ) :
      massGradNormSq (rhoEnh D F.cr F.m)
          (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2) (fun v => (W v t).val) ≤
        massGradNormSq (rhoEnh D F.cr F.m)
          (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2) (fun v => (F.Yw v t).val) := by
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : (compWord F.m v.1).length = 0
    · simp only [W, ite_eq_left hv, le_refl]
    · simp only [W, ite_eq_right hv, Submodule.coe_zero, gradFactorialNormSq,
        WithLp.ofLp_zero, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, Finset.sum_const_zero, mul_zero]
      exact mul_nonneg (inv_nonneg.mpr (hπ v).le)
        (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)
  have hint := integral_mono
    (CycleComparison.Error.integrable_massGradNormSq (rhoEnh D F.cr F.m) _ W hW)
    (CycleComparison.Error.integrable_massGradNormSq (rhoEnh D F.cr F.m) _ F.Yw hw) hpoint
  have hselected := mul_le_mul_of_nonneg_left hint hν
  have hfull' : F.sourceDissipation true ≤ F.initialNorm ^ 2 := by
    simpa only [SourceLayerEnergyStatement, Frame.layerGain, ite_true, one_mul] using hfull
  apply le_trans (b := F.sourceDissipation true) ?_ hfull'
  simpa only [EmptyWordDissipationStatement, prefixDissipation, Frame.sourceDissipation,
    Bool.true_or, ite_true, W, apply_ite Subtype.val, Submodule.coe_zero] using hselected

/-- The exact length-source inequality with both routine ingredients discharged.
Only the forced copied-block estimate remains. -/
theorem length_source_energy_of_copied_blocks (F : Frame D hr Dm bw j₀) (C : ℝ)
    (hE : 0 < D.eps (F.m - 1)) (hν : 0 ≤ D.κ (F.m - 1))
    (hπ : ∀ v : CompIn F.Gr.comps, 0 < F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
    (hw : ∀ v, MemLp (F.Yw v) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hrows : WordLengthRowsStatement F C) (hfull : SourceLayerEnergyStatement F true 1)
    (hblock : CopiedWordBlockEnergyStatement F) :
    SourceLayerEnergyStatement F false ((4 * C) ^ F.J) :=
  length_source_energy_of_ingredients prefix_dissipation_induction F C hE hrows
    (empty_word_dissipation_of_contraction F hν hπ hw hfull) hblock
end

end AVRegularity.Construction.Preservation.Frontier.LengthEnergy
end
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier.LengthEnergy

/-! Actual provenance gives a two-diagonal decomposition in word length: copied edges
preserve length, fresh edges increase it by one. The excluded-column flux of one retained
block is therefore exactly the previous prefix, before any kernel-lift identification. -/

section
open KernelEnergy FullLift Ledger
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Inclusion of a retained component in the extended family. -/
abbrev extendedComp (F : Frame D hr Dm bw j₀) (v : CompIn F.Gr.comps) : CompIn F.G'.comps :=
  ⟨v.1, (Finset.mem_filter.mp v.2).1⟩

/-- Components in one retained word-length block. -/
def inWordBlock (F : Frame D hr Dm bw j₀) (l : ℕ) (v : CompIn F.Gr.comps) : Prop :=
  (compWord F.m v.1).length = l

/-- Every actual edge preserves word length or increases it by one, including zero letters.
The degenerate cases are included: empty/edgeless stages are vacuous, l=1 has source length zero,
and a copied diagonal edge is allowed. No positivity of an edge or its physical coefficient is
needed. -/
theorem actual_edge_word_lengths (F : Frame D hr Dm bw j₀)
    {P : ProvParams} {Mn : SuccMenu} (hs : IsActualSuccessor D P Mn F.G F.G')
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale)
    (hm : F.G.level = F.m) (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u) :
    (compWord F.m v.1).length = (compWord F.m u.1).length ∨
      (compWord F.m v.1).length = (compWord F.m u.1).length + 1 := by
  let E := Classical.choice (actual_sources hs)
  let e : LedgerEdge F.G' := ⟨v, u, γ⟩
  have hmem := source_old_mem (E.source e) (E.valid e)
  have hsrc := (parent_word_succComp hs.1 _ (hold _ hmem.2) (E.source e).word).2
  have htgt := (parent_word_succComp hs.1 _ (hold _ hmem.1) (E.source e).newWord).2
  change compWord F.G.level ((E.source e).srcComp F.G.level) = _ at hsrc
  change compWord F.G.level ((E.source e).tgtComp F.G.level) = _ at htgt
  rw [E.src e, hm] at hsrc
  rw [E.tgt e, hm] at htgt
  rw [hsrc, htgt]
  cases he : (E.source e).letter? with
  | none => exact Or.inl (by simp only [SuccSource.newWord, he])
  | some a => exact Or.inr (by
      simp only [SuccSource.newWord, he, List.length_append, List.length_singleton])

/-- A nonempty retained word has zero initial trace.
The degenerate cases are included: empty and J=0 blocks are vacuous, and no covariance operator
estimate is used. -/
theorem word_block_trace_zero (F : Frame D hr Dm bw j₀) (l : ℕ) (hl : 1 ≤ l)
    (hm : 1 ≤ F.m)
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.m ≤ e.scale)
    (hzero : ∀ v : CompIn F.Gr.comps, v.1 ∉ F.G.comps → F.Y0 v = 0)
    (v : {v // inWordBlock F l v}) : F.Y0 v.1 = 0 := by
  apply hzero
  intro hv
  have hword := (InitialValue.compParent_eq_self hm (hold _ hv)).2
  have hlen : (compWord F.m v.1.1).length = l := v.2
  rw [hword, List.length_nil] at hlen
  omega

/-- A finite component block sum is the corresponding selected full sum. -/
theorem word_block_subtype_sum {ι V : Type*} [Fintype ι] [AddCommMonoid V]
    (sel : ι → Prop) [DecidablePred sel] (f : ι → V) :
    (∑ i : {i // sel i}, f i) = ∑ i, if sel i then f i else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter sel) (by simp) f,
    Finset.sum_filter]

/-- The crossing flux of the retained block is the literal preceding prefix. This is a
pointwise finite-sum identity for the supplied extended lifts, not a time-a.e. assertion.
The degenerate cases are included: empty and singleton families, l=1, k=0, zero data and identity
geometry; no J+1 interior block is used. -/
theorem retained_crossing_eq_prefix (F : Frame D hr Dm bw j₀)
    {P : ProvParams} {Mn : SuccMenu} (hs : IsActualSuccessor D P Mn F.G F.G')
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale)
    (hm : F.G.level = F.m) (l : ℕ) (hl : 1 ≤ l) (hlJ : l ≤ F.J)
    (R : TorusKernelOperator (h := fun v : CompIn F.Gr.comps => hr v.1.root)
      (Γ := F.Gr.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm)
    (hB : R.B = fun (v u : CompIn F.Gr.comps) (γ : F.Gr.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => F.Gr.physCoeff v u γ d.1)
    (v : {v // inWordBlock F l v}) (t : ℝ) (x : Vec 2) :
    crossingKernelFlux R (inWordBlock F l)
        (fun v u γ => F.yom (extendedComp F v) (extendedComp F u) γ) v t x =
      omittedFlux F.G' F.k (IsRetained F.m F.H (l - 1)) F.yom (extendedComp F v.1) t x := by
  have hsub : F.Gr.comps ⊆ F.G'.comps := Finset.filter_subset _ _
  unfold omittedFlux
  rw [finite_own_component_sum hsub _ ?_]
  · let g (u : CompIn F.Gr.comps) : PiLp 2 (fun _ : Fin 2 => hr v.1.1.root) :=
      ∑ γ : F.Gr.fam.Γ v.1 u, ∑ d : ↥(Finset.Icc 2 Dm),
        R.B v.1 u γ d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (F.yom (extendedComp F v.1) (extendedComp F u) γ t).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ x)
    change (∑ u : {u // ¬inWordBlock F l u}, g u.1) = _
    trans ∑ u : CompIn F.Gr.comps, if ¬inWordBlock F l u then g u else 0
    · exact word_block_subtype_sum (fun u => ¬inWordBlock F l u) g
    dsimp only [g]
    apply Finset.sum_congr rfl
    intro u _
    have hu := (Finset.mem_filter.mp u.2).2
    by_cases hlen : inWordBlock F l u
    · have hn : ¬IsRetained F.m F.H (l - 1) u.1 := by
        intro hh
        have hlen' : (compWord F.m u.1).length = l := hlen
        have hh' := hh.2
        omega
      simp only [hlen, not_true_eq_false, ite_false, hn]
    · rw [ite_eq_left hlen]
      by_cases hret : IsRetained F.m F.H (l - 1) u.1
      · rw [ite_eq_left hret]
        apply Finset.sum_congr rfl
        intro γ _
        apply Finset.sum_congr rfl
        intro d _
        rw [hB]
        rfl
      · rw [ite_eq_right hret]
        apply Finset.sum_eq_zero
        intro γ _
        exfalso
        have hh := actual_edge_word_lengths F hs hold hm (extendedComp F v.1) (extendedComp F u) γ
        have hv : (compWord F.m v.1.1).length = l := v.2
        have hnot : (compWord F.m u.1).length ≠ l := hlen
        have hul : (compWord F.m u.1).length = l - 1 := by
          change (compWord F.m v.1.1).length = (compWord F.m u.1).length ∨
            (compWord F.m v.1.1).length = (compWord F.m u.1).length + 1 at hh
          omega
        exact hret ⟨hu.1, hul.le⟩
  · intro u hu
    have hn : ¬IsRetained F.m F.H (l - 1) u.1 := by
      intro hh
      exact hu (Finset.mem_filter.mpr ⟨u.2, hh.1, hh.2.trans (by omega)⟩)
    simp only [hn, ite_false]
end

/-! Identify the canonical block forcing with the supplied fresh-prefix row only on the
common good time set. Exceptional-time representatives never enter an energy integral. -/

section
open KernelEnergy FullLift
open scoped Classical
section Generic
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {k D : ℕ}

/-- Canonical block forcing equals the excluded-column supplied flux almost everywhere
in time and space. The degenerate cases are included: empty and full selections and zero data;
supplied higher lifts may be changed at exceptional times, while the canonical weak solution is
unchanged. -/
theorem block_carrier_forcing_raw
    (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D) (sel : ι → Prop)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (hy : ∀ i j α, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (y i j α t).val (valueIndex2 (k + D - 1)) =
        P.S i j α t ((P.C i j α).compLp ((w j t).val (valueIndex2 (k + 1)))))
    (i : {i // sel i}) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (blockCarrierForcing P sel w i t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict unitCube]
        crossingKernelFlux P sel y i t := by
  let R := restrictKernelComponents P sel
  have hysub : ∀ i j α, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (y i.1 j.1 α t).val (valueIndex2 (k + D - 1)) =
        R.S i j α t ((R.C i j α).compLp ((w j.1 t).val (valueIndex2 (k + 1)))) :=
    fun i j => hy i.1 j.1
  filter_upwards [P.inputRawFlux_eq_kernelRawFlux_ae w y hy i.1,
    R.inputRawFlux_eq_kernelRawFlux_ae (fun j => w j.1) (fun i j => y i.1 j.1) hysub i,
    ae_restrict_mem measurableSet_Icc] with t hfull hsub ht
  filter_upwards [Providers.WeakGen.Comparison.torusHk_jet_sub_ae
      (P.carrierFlux w i.1 t) (R.carrierFlux (fun j => w j.1) i t) (valueIndex2 k),
    P.carrierFlux_raw w i.1 t ht,
    R.carrierFlux_raw (fun j => w j.1) i t ht] with x hdiff hleft hright
  change (P.carrierFlux w i.1 t - R.carrierFlux (fun j => w j.1) i t).toFunction.jet
    (valueIndex2 k) x = _
  rw [hdiff, hleft, hright, ← hfull, ← hsub]
  have hsplit : P.inputRawFlux y i.1 t x =
      R.inputRawFlux (fun i j => y i.1 j.1) i t x + crossingKernelFlux P sel y i t x :=
    (Fintype.sum_subtype_add_sum_subtype sel (fun j : ι =>
      ∑ α : Γ i.1 j, ∑ d : ↥(Finset.Icc 2 D), P.B i.1 j α d t x
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (y i.1 j α t).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ x))).symm
  rw [hsplit, add_sub_cancel_left]
end Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The canonical external forcing of an actual retained block is the existing fresh-prefix
representative in the carrier, for almost every time. The degenerate cases are included: l=1, J=0
(no interior block), empty and singleton fibres, k=0, identity metric, zero data and edgeless
stages. -/
theorem retained_block_forcing_eq_row (F : Frame D hr Dm bw j₀)
    {P : ProvParams} {Mn : SuccMenu} (hs : IsActualSuccessor D P Mn F.G F.G')
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale)
    (hm : F.G.level = F.m) (l : ℕ) (hl : 1 ≤ l) (hlJ : l ≤ F.J)
    (R : TorusKernelOperator (h := fun v : CompIn F.Gr.comps => hr v.1.root)
      (Γ := F.Gr.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm)
    (hB : R.B = fun (v u : CompIn F.Gr.comps) (γ : F.Gr.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => F.Gr.physCoeff v u γ d.1)
    (hy : ∀ v u (γ : F.Gr.fam.Γ v u), ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
      (F.yom (extendedComp F v) (extendedComp F u) γ t).val (valueIndex2 (F.k + Dm - 1)) =
        R.S v u γ t ((R.C v u γ).compLp ((F.Yw u t).val (valueIndex2 (F.k + 1)))))
    (OF : F.RowFlux) (hOF : RealizesPrefix F l OF)
    (v : {v // inWordBlock F l v}) :
    blockCarrierForcing R (inWordBlock F l) F.Yw v =ᵐ[volume.restrict (Set.Icc F.tp F.tf)]
      OF (extendedComp F v.1) := by
  filter_upwards [block_carrier_forcing_raw R (inWordBlock F l) F.Yw
      (fun v u γ => F.yom (extendedComp F v) (extendedComp F u) γ) hy v,
    ae_restrict_mem measurableSet_Icc] with t ht htI
  apply torusCarrier_eq_of_value_ae
  have hv : compGrade v.1.1 ≤ F.H ∧ (compWord F.m v.1.1).length = l :=
    ⟨(Finset.mem_filter.mp v.1.2).2.1, v.2⟩
  filter_upwards [ht, hOF (extendedComp F v.1) t htI] with x hx hrow
  change _ = _ at hrow
  rw [ite_eq_left hv] at hrow
  exact hx.trans ((retained_crossing_eq_prefix F hs hold hm l hl hlJ R hB v t x).trans hrow.symm)
end

/-! The forced estimate on each copied word-length block, with its canonical forcing
identified almost everywhere with the proved fresh-prefix representative. -/

section
open KernelEnergy FullLift
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The gradient mass of a component subtype is the gradient mass of its zero extension. -/
theorem word_block_gradient_mass (F : Frame D hr Dm bw j₀) (l : ℕ) (t : ℝ) :
    massGradNormSq (rhoEnh D F.cr F.m)
      (fun v : {v // inWordBlock F l v} => F.Gr.mass F.law v.1 / F.Gr.marker F.law v.1 ^ 2)
      (fun v => (F.Yw v.1 t).val) =
    massGradNormSq (rhoEnh D F.cr F.m)
      (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
      (fun v => if (compWord F.m v.1).length = l then (F.Yw v t).val else 0) := by
  unfold massGradNormSq
  let g (v : CompIn F.Gr.comps) :=
    (F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)⁻¹ *
      gradFactorialNormSq (rhoEnh D F.cr F.m) (F.Yw v t).val
  change (∑ v : {v // inWordBlock F l v}, g v.1) = _
  trans ∑ v : CompIn F.Gr.comps, if inWordBlock F l v then g v else 0
  · exact word_block_subtype_sum (inWordBlock F l) g
  dsimp only [g]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : inWordBlock F l v
  · rw [ite_eq_left hv]
    have hv' : (compWord F.m v.1).length = l := hv
    rw [ite_eq_left hv']
  · have hv' : (compWord F.m v.1).length ≠ l := hv
    simp only [hv, ite_false, ite_eq_right hv', gradFactorialNormSq,
      WithLp.ofLp_zero, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, mul_zero]

/-- A block of the extended row flux has no larger marked mass than the whole row family. -/
theorem word_block_row_mass_le (F : Frame D hr Dm bw j₀) (l : ℕ)
    (hπ : ∀ v : CompIn F.G'.comps, 0 < F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    (OF : F.RowFlux) (t : ℝ) :
    massNormSq (rhoEnh D F.cr F.m)
      (fun v : {v // inWordBlock F l v} => F.Gr.mass F.law v.1 / F.Gr.marker F.law v.1 ^ 2)
      (fun v => (OF (extendedComp F v.1) t).val) ≤
    massNormSq (rhoEnh D F.cr F.m)
      (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (OF v t).val) := by
  unfold massNormSq
  apply Finset.sum_le_sum_of_injOn (fun v : {v // inWordBlock F l v} => extendedComp F v.1)
  · intro v _ u _ h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : CompIn F.G'.comps => z.1) h))
  · intro v _
    exact Finset.mem_univ _
  · intro v _
    exact le_rfl
  · intro v _ _
    exact mul_nonneg (inv_nonneg.mpr (hπ v).le) (factorialNormSq_nonneg _ _)

/-- Copied word-length energy from actual provenance, the native operator and the original
retained solution. Only the fresh forcing is estimated; the copied block remains inside the
contractive principal operator.
The degenerate cases are included: empty and singleton blocks, l=1, J=0, k=0, identity
geometry, zero data and edgeless seed. All forcing integrals are integrable; equality with supplied
lifts is only used a.e. in time. -/
theorem copied_word_block_energy_of_operator (F : Frame D hr Dm bw j₀)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    {P : ProvParams} {Mn : SuccMenu} (hactual : IsActualSuccessor D P Mn F.G F.G')
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale)
    (hlevel : F.G.level = F.m)
    (R : TorusKernelOperator (h := fun v : CompIn F.Gr.comps => hr v.1.root)
      (Γ := F.Gr.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm)
    (hB : R.B = fun (v u : CompIn F.Gr.comps) (γ : F.Gr.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => F.Gr.physCoeff v u γ d.1)
    (hπ : R.π = fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
    (drift : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc F.tp F.tf, ContDiff ℝ (↑(⊤ : ℕ∞)) (drift t))
    (hp : ∀ t ∈ Set.Icc F.tp F.tf, AVenhance.IsZ2Periodic (drift t))
    (hm : Measurable (fun p : Set.Icc F.tp F.tf × Vec 2 => drift p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc F.tp F.tf, ∀ x, ‖drift t x‖ ≤ V)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * rhoEnh D F.cr F.m / lam ≤ 1 / 2)
    (hstrain : α * B * rhoEnh D F.cr F.m ^ 2 ≤ D.κ (F.m - 1) / 8)
    (hd : ∀ t ∈ Set.Icc F.tp F.tf, ∀ x, ∑ q : Fin 2, fderiv ℝ (drift t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc F.tp F.tf, ∀ l, 1 ≤ l → l ≤ F.k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (drift t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk F.k (hr v.1.root))
    (hsol : IsCoupledWeakSolutionTorus (D.κ (F.m - 1)) F.tp F.tf drift 0 (fun _ => F.k)
      TorusKernelOperator.noLocalCoefficient F.Y0 (R.carrierFlux F.Yw) (fun _ _ => 0) U F.Yw)
    (hzero : ∀ v : CompIn F.Gr.comps, v.1 ∉ F.G.comps → F.Y0 v = 0)
    (hy : ∀ v u (γ : F.Gr.fam.Γ v u), ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
      (F.yom (extendedComp F v) (extendedComp F u) γ t).val (valueIndex2 (F.k + Dm - 1)) =
        R.S v u γ t ((R.C v u γ).compLp ((F.Yw u t).val (valueIndex2 (F.k + 1))))) :
    CopiedWordBlockEnergyStatement F := by
  intro l hl hlJ OF hOF hLp
  have hmass (v : CompIn F.G'.comps) : 0 < F.G'.mass F.law v / F.G'.marker F.law v ^ 2 :=
    div_pos (Buffer.birth_compMass_pos hq hΛ F.law v.1)
      (sq_pos_of_pos (Buffer.birth_compMarker_pos hq hΛ F.law v.1))
  have hf (v : CompIn F.Gr.comps) (hv : inWordBlock F l v) : F.Y0 v = 0 :=
    word_block_trace_zero F l hl (hlevel ▸ hactual.1) (hlevel ▸ hold) hzero ⟨v, hv⟩
  have he := kernel_forced_block_energy R (inWordBlock F l) drift hv hp hm V hV hvb
    α B lam hα hBdrift hlam hsmall hstrain hd hjets F.Y0 U F.Yw hf hsol
  have hforcing := retained_block_forcing_eq_row F hactual hold hlevel l hl hlJ R hB hy OF hOF
  let RF := blockCarrierForcing R (inWordBlock F l) F.Yw
  have hRF := block_carrier_forcing_memLp R (inWordBlock F l) F.Yw hsol.2.1
  have hineq : ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
      massNormSq (rhoEnh D F.cr F.m) (fun v : {v // inWordBlock F l v} => R.π v.1)
          (fun v => (RF v t).val) ≤
        massNormSq (rhoEnh D F.cr F.m)
          (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (OF v t).val) := by
    filter_upwards [ae_all_iff.mpr hforcing] with t ht
    simp only [RF, ht, hπ]
    exact word_block_row_mass_le F l hmass OF t
  have hint := integral_mono_ae
    (CycleComparison.Error.integrable_massNormSq (rhoEnh D F.cr F.m) _ RF hRF)
    (CycleComparison.Error.integrable_massNormSq (rhoEnh D F.cr F.m) _ OF hLp) hineq
  have he' : prefixDissipation F l ≤
      16 * (D.κ (F.m - 1))⁻¹ * (∫ t in Set.Icc F.tp F.tf,
        massNormSq (rhoEnh D F.cr F.m) (fun v : {v // inWordBlock F l v} => R.π v.1)
          (fun v => (RF v t).val)) := by
    simpa only [prefixDissipation, hπ, word_block_gradient_mass] using he
  exact he'.trans (by
    simpa only [Frame.rowEnergy, mul_assoc] using
      mul_le_mul_of_nonneg_left hint
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (inv_nonneg.mpr R.diffusivity_pos.le)))
end

/-! Instantiate the copied-block energy and scalar induction uniformly. The indexed fresh
prices are reused from LengthPrice, and the full native operator is restricted to the retained
components with its original constants. -/

section
open FullLift KernelEnergy AVRegularity.Construction.Preservation.Assembly RetainedEnergy
open scoped Classical

/-- Fixed-stage length-source energy from the extended native operator and indexed rows.
The degenerate cases are included: empty and singleton families, J=0, k=0, zero data, identity
metric and an edgeless seed. The principal retained operator keeps the extended operator's
constants. -/
theorem length_source_energy_of_extended_operator
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (F : Frame D hr Dm bw j₀) (hqD : 1 < D.q) (hΛD : 128 ≤ D.Λ)
    (P : ProvParams) (Mn : SuccMenu) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (hactual : IsActualSuccessor D P Mn F.G F.G')
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale)
    (hlevel : F.G.level = F.m)
    (Rk : TorusKernelOperator (h := fun v : CompIn F.G'.comps => hr v.1.root)
      (Γ := F.G'.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm)
    (hB : Rk.B = fun (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => F.G'.physCoeff v u γ d.1)
    (hC : Rk.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root))
    (hS : Rk.S = F.G'.sysS P seedK freshK φ₀ hφ₀)
    (hπ : Rk.π = fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (αv B lam : ℝ) (hαv : 0 ≤ αv) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmallD : B * rhoEnh D F.cr F.m / lam ≤ 1 / 2)
    (hstrain : αv * B * rhoEnh D F.cr F.m ^ 2 ≤ D.κ (F.m - 1) / 8)
    (hjets : ∀ t ∈ Set.Icc F.tp F.tf, ∀ j, 1 ≤ j → j ≤ F.k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) j x‖ ≤
        αv * B ^ j * (j.factorial : ℝ) * lam ^ ((1 : ℤ) - j))
    (Y : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk F.k (hr v.1.root))
    (Yk : ∀ v u (_ : F.Gr.fam.Γ v u), ℝ → TorusHk (F.k + Dm - 1) (hr u.1.root))
    (hsol : F.Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (F.m - 1)) (streamVel φ)
      F.k F.tp F.tf F.Y0 (fun _ _ => 0) (fun _ _ => 0) Y F.Yw Yk)
    (hzero : ∀ v : CompIn F.Gr.comps, v.1 ∉ F.G.comps → F.Y0 v = 0)
    (hy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
          Rk.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.mpr ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1))))
    (Cp : ℝ) (hrows : WordLengthRowsStatement F Cp) (hE : 0 < D.eps (F.m - 1)) :
    SourceLayerEnergyStatement F false ((4 * Cp) ^ F.J) := by
  classical
  let emb : CompIn F.Gr.comps ↪ CompIn F.G'.comps :=
    ⟨extendedComp F, fun _ _ hh => Subtype.ext (congrArg (fun z : CompIn F.G'.comps => z.1) hh)⟩
  let Rret : TorusKernelOperator (h := fun v : CompIn F.Gr.comps => hr v.1.root)
      (Γ := F.Gr.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm :=
    reindexKernelComponents Rk emb
  have hBret : Rret.B = fun (v u : CompIn F.Gr.comps) (γ : F.Gr.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => F.Gr.physCoeff v u γ d.1 := by
    change (fun v u => Rk.B (extendedComp F v) (extendedComp F u)) = _
    rw [hB]
    rfl
  have hCret : Rret.C = fun (v u : CompIn F.Gr.comps) (_ : F.Gr.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root) := by
    change (fun v u => Rk.C (extendedComp F v) (extendedComp F u)) = _
    rw [hC]
    rfl
  have hSret : Rret.S = F.Gr.sysS P seedK freshK φ₀ hφ₀ := by
    change (fun v u => Rk.S (extendedComp F v) (extendedComp F u)) = _
    rw [hS]
    rfl
  have hπret : Rret.π = fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2 := by
    change (fun v => Rk.π (extendedComp F v)) = _
    rw [hπ]
    rfl
  have hforced := native_reg_solution_forced_at_order P seedK freshK φ₀ hφ₀ F.Gr Rret
    hBret hCret hSret hφ F.Y0 Y F.Yw Yk hsol
  have hhyret : ∀ v u (γ : F.Gr.fam.Γ v u), ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
      (F.yom (extendedComp F v) (extendedComp F u) γ t).val
          (valueIndex2 (F.k + Dm - 1)) =
        Rret.S v u γ t ((Rret.C v u γ).compLp ((F.Yw u t).val (valueIndex2 (F.k + 1)))) := by
    intro v u γ
    filter_upwards [hy (extendedComp F v) (extendedComp F u) γ
      (Finset.mem_filter.mp u.2).2] with t ht
    change _ = Rk.S (extendedComp F v) (extendedComp F u) γ t
      ((Rk.C (extendedComp F v) (extendedComp F u) γ).compLp
        ((F.Yw u t).val (valueIndex2 (F.k + 1))))
    rw [hC]
    dsimp only
    rw [Providers.WeakGen.Comparison.id_compLp_eq]
    exact ht
  obtain ⟨hv, hp, hddiv, ⟨V, hV⟩, hmeas⟩ := Buffer.stream_kernel_drift_data hφ F.tp F.tf
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hvb : ∀ t ∈ Set.Icc F.tp F.tf, ∀ x, ‖streamVel φ t x‖ ≤ max V 0 :=
    fun t ht x => (hV t ht x).trans (le_max_left _ _)
  have hblocks := copied_word_block_energy_of_operator F hqD hΛD hactual hold hlevel
    Rret hBret hπret (streamVel φ) hv hp hmeas (max V 0) hV0 hvb
    αv B lam hαv hBdrift hlam hsmallD hstrain hddiv hjets Y hforced hzero hhyret
  have heFull := native_reg_solution_homogeneous_contraction P seedK freshK φ₀ hφ₀ F.Gr
    Rret hBret hCret hSret hφ αv B lam hαv hBdrift hlam hsmallD hstrain hjets
    F.Y0 Y F.Yw Yk hsol F.tf ⟨Rk.htime, le_rfl⟩
  have hin : F.initialNorm ^ 2 =
      massNormSq (rhoEnh D F.cr F.m) Rret.π (fun v => (F.Y0 v).val) := by
    unfold Frame.initialNorm weightedNorm
    rw [← hπret, Real.sq_sqrt (CoupledEnergy.Variational.massNormSq_nonneg _ _ Rret.hπ _)]
  rw [← hin] at heFull
  have hfull : SourceLayerEnergyStatement F true 1 := by
    have hI : 0 ≤ ∫ t in Set.Icc F.tp F.tf,
        massGradNormSq (rhoEnh D F.cr F.m) Rret.π (fun v => (F.Yw v t).val) :=
      integral_nonneg fun t => CoupledEnergy.Variational.massGradNormSq_nonneg _ _ Rret.hπ _
    have hi := mul_nonneg Rret.diffusivity_pos.le hI
    have hn0 := CoupledEnergy.Variational.massNormSq_nonneg (rhoEnh D F.cr F.m) _ Rret.hπ (fun v => (Y v F.tf).val)
    have hdrop : D.κ (F.m - 1) * (∫ t in Set.Icc F.tp F.tf,
        massGradNormSq (rhoEnh D F.cr F.m) Rret.π (fun v => (F.Yw v t).val)) ≤ F.initialNorm ^ 2 := by
      linarith only [heFull, hi, hn0]
    simpa only [SourceLayerEnergyStatement, Frame.sourceDissipation, Frame.layerGain,
      Bool.true_or, ite_true, one_mul, hπret] using hdrop
  exact length_source_energy_of_copied_blocks F Cp hE Rret.diffusivity_pos.le
    (fun v => by simpa only [hπret] using Rret.hπ v) hsol.2.1 hrows hfull hblocks
end

/-! Instantiate the copied-block energy and scalar induction uniformly. The indexed fresh
prices are reused from LengthPrice, and the full native operator is restricted to the retained
components with its original constants. -/

section
open FullLift KernelEnergy AVRegularity.Construction.Preservation.Assembly RetainedEnergy
open scoped Classical

/-- Uniform data adapter for length-source dissipation. The degenerate cases are included:
empty and singleton families, J=0, k=0, zero data, identity metric and edgeless seed; constants
precede all stage data. -/
theorem length_source_energy_at_data {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Λl Λ : ℕ)
    (hlength : UniformRecordLengths α q ζ Λl) (hΛ : Λl ≤ Λ) (h128 : 128 ≤ Λ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ) (hbw : 0 < bw)
    (Q T₀ Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ)
    (σ₀ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr : ℝ) (hCI : 0 ≤ CI) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ₀) (hτe : 0 < τe)
    (hcker : ∀ j, j + 2 ≤ succSchedD D₀ N p (H + 1) → 0 ≤ kI.cker j) (mc : ℕ)
    (hc : ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (hprod : kI.Hprod = kI.G0 + H + 1) (hc0pos : 0 < kI.c₀) (hc0le : kI.c₀ ≤ 1)
    (_hcrpos : 0 < kI.cr) (hcrle : kI.cr ≤ 1) (mr : ℕ) (hmr : 2 ≤ mr)
    (hradius : EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr) (md : ℕ)
    (hdrift : EnhancedDriftAt α q ζ Λ kI.cr md)
    (Cu : ℝ) (hscale : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu)
    (A : ℝ) (hA : 0 ≤ A) (mo : ℕ)
    (hop : NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo)
    (ma : ℕ)
    (habs : ∀ m, ma ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8)
    : ∃ (C : ℝ) (mStar : ℕ),
      FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
        r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar false (fun _rows _readout source => source) := by
  classical
  obtain ⟨Cp, mp, hprice⟩ := LengthPrice.length_prefix_prices_at_data
    hα₀ hα₁ hs₀ hs₁ hq hζ Λl Λ hlength hΛ h128 φ₀ hφ₀ bw hbw Q T₀ Ce τe kS
    r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr hCI hCw hσ hτe
    hcker mc hc hprod hc0pos hc0le _hcrpos hcrle mr hmr hradius md hdrift
    Cu hscale A hA mo hop ma habs
  refine ⟨(4 * Cp) ^ J, max mp (max mc (max mr (max md (max (mo + 3)
    (max ma (j₀ + 3)))))), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual tp Preg hprep
    f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hyom
  have hmc : mc ≤ m := by omega
  have hmr' : mr ≤ m := by omega
  have hmd' : md ≤ m := by omega
  have hmo' : mo + 1 ≤ m - 1 := by omega
  have hma : ma ≤ m := by omega
  have hjGr' : j₀ ≤ m - 1 := by omega
  have hm2 : 2 ≤ m := by omega
  have hiGr' : 1 ≤ m - 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hmterm : m ≤ D.term := by rw [hterm]; exact hn.trans hnM.le
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact h128
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'
  have hGrlevel : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hGrlevelterm : Gr.level ≤ D.term := by omega
  have hGrI := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hnat, hshift, hslot, hctx, hled, hker⟩ := hGrI
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    AVRegularity.Providers.CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hprod
      (AVRegularity.Providers.CascadeInvariants.grade_le_of_succ
        (AVRegularity.Providers.CascadeInvariants.grade_le_of_cascade hseed.2.1 hcascade) hactual v)
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenG := hlength hr D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ Mn Cw kI.cr σ₀ (succEta0 α q s) N p hcrle seed G hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcascade (hlevel.symm ▸ hm1)
  have hscl := hscale D hDα hDq hDΛ hDζ hbandD m hm2 hmterm
  have hlenGr := extended_successor_record_lengths P Mn G G' hactual hG.2.1 hlenG
    (EntryScales.epsilon_antitone hqD (by omega) (by rw [hactual.2.1]; omega))
    (by
      change freshLength D kI.cr (G.level - 1) ≤ D.eps G'.level
      rw [hactual.2.1, hlevel]
      simpa only [Nat.sub_add_cancel hm1] using
        AVRegularity.Providers.CascadeInvariants.freshLength_le_eps_of_passScales hcrle
          (show AVRegularity.Providers.CascadeInvariants.PassScales D ((m - 1) + 1) Cu from
            (Nat.sub_add_cancel hm1).symm ▸ hscl))
  have he (l : ℕ) : 0 < D.eps l := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ (l : ℕ) (hl : l ≤ D.term) : 0 < D.κ l :=
    CycleReference.bandChain_pos (by omega) hζD hbandD hl
  have ha (l : ℕ) : 0 < ocA D.α D.q D.Λ l := Real.rpow_pos_of_pos (he l) _
  have hrs (l : ℕ) (hl : l ≤ D.term) :
      0 < rhoStar D kI.c₀ l ∧ rhoStar D kI.c₀ l ≤ D.eps l := by
    have hh := Buffer.molecular_radius_bounds hc0pos (he l) (hκ l hl) (ha l)
    exact ⟨hh.1, hh.2.1.trans (mul_le_of_le_one_left (he l).le hc0le)⟩
  have hrhos := hradius D hDα hDq hDΛ hDζ hbandD m hmr' hmterm
  have hρe : rhoEnh D kI.cr m ≤ D.eps Gr.level := by
    rw [hGrlevel]
    exact hrhos.trans (hrs (m - 1) (by omega)).2
  have hρE : rhoEnh D kI.cr m ≤ D.eps (Gr.level - 1) :=
    hρe.trans (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hd := hdrift D.Φ hseq M D.κ hband m hmd' (hn.trans hnM.le)
  have hρpos : 0 < rhoEnh D kI.cr m := by
    simpa only [rhoEnh, hDα, hDq, hDΛ] using hd.2.1
  have htptf : tp ≤ tf := by
    have hh := hprep.2.2.1
    rw [hlevel, hDα, hDq, hDΛ] at hh
    exact hh.trans hwindow
  have hsub : Set.Icc tp tf ⊆ Set.Icc (tA + 3 * ocTau α q Λ m) tf := by
    intro t ht
    exact ⟨(hdelay.trans hprep.2.1).trans ht.1, ht.2⟩
  have hSzero : ∀ v u (γ : Gr.fam.Γ v u), IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0
      (succSchedD D₀ N p (H + 1)) tp tf kI.cker
      (Gr.kernelOf P seedK freshK v u γ).width (Gr.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
    intro v u γ
    exact Buffer.spatialRegularizerTorus_time_restrict ((hker v u γ).2 _ hρpos) hsub
  have hkap : D.kap Gr.level = D.κ (m - 1) := by
    change D.κ (min Gr.level D.term) = _
    rw [Nat.min_eq_left hGrlevelterm, hGrlevel]
  have hsmall : A * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8 := by
    simpa only [OCData.eps, hDq, hDΛ] using habs m hma
  have hlengthop : ∀ v u (γ : Gr.fam.Γ v u), 3 ≤ (Gr.fam.identity v u γ).maxOrder →
      (Gr.fam.identity v u γ).record.length ≤ D.eps (Gr.level - 1) := by
    intro v u γ hj
    have hb : 1 ≤ (Gr.fam.identity v u γ).record.birthExcess := by
      have hh := (Gr.fam.identity v u γ).le_birth
      omega
    exact (hlenGr v u γ hb).trans
      (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hop' := hop hr D hDα hDq hDΛ hDζ hseq j₀ Mnat Gr kI hctx hnat hshift
    (hGrlevel.symm ▸ hmo') (hGrlevel.symm ▸ hiGr') (hGrlevel.symm ▸ hjGr')
    (he _) (he _) (by rw [hkap]; exact hd.1)
    hslot hmGr hm2Gr P seedK freshK (fun v u γ => (hker v u γ).1) φ₀ hφ₀ tp tf
    (rhoEnh D kI.cr m) (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)
    (Gr.mass law) (Gr.marker law) htptf hρpos hρE hρe hlengthop
    (fun v => Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD law v.1) hled hsmall.le hSzero
  rw [hkap] at hop'
  obtain ⟨R, hB, hC, hS, hπ, hRadius, hcR, _hθ⟩ := hop' (Gr.marker law) (Or.inr rfl)
  have hSall : ∀ v u γ, IsSpatialRegularizerTorus (rhoEnh D kI.cr m) k
      (succSchedD D₀ N p (H + 1)) tp tf R.c (R.r v u γ) (R.S v u γ) := by
    intro v u γ
    rw [hRadius, hcR, hS]
    exact spatial_regularizer_all_orders _ _ _ _ _ _ _ (hSzero v u γ) k
  let Rk := kernelOperator_order_restrict R hk hSall
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
      cr := kI.cr, η := succEta0 α q s,
      θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
      θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
      tp := tp, tf := tf, Y0 := Y0, Yw := Yw, yom := yom }
  have hφ : IsAdmissibleStream (D.Φ (m - 1)) := (hseq.2 m hm1).choose
  let αv := Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)
  have hαv : 0 ≤ αv := mul_nonneg Buffer.actualDriftJetConstant_nonneg
    (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hsmallD : 1024 * rhoEnh D kI.cr m / D.eps (m - 1) ≤ 1 / 2 := by
    simpa only [rhoEnh, OCData.eps, hDα, hDq, hDΛ] using hd.2.2.1
  have hstrain : αv * 1024 * rhoEnh D kI.cr m ^ 2 ≤ D.κ (m - 1) / 8 := by
    simpa only [αv, rhoEnh, hDα, hDq, hDΛ] using hd.2.2.2.1
  have hjets : ∀ t ∈ Set.Icc tp tf, ∀ j, 1 ≤ j → j ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (m - 1)) t)) j x‖ ≤
        αv * 1024 ^ j * (j.factorial : ℝ) * D.eps (m - 1) ^ ((1 : ℤ) - j) := by
    intro t _ j hj _ x
    simpa only [αv, OCData.eps, hDq, hDΛ] using hd.2.2.2.2 t j hj x
  have hold := InitialValue.cascade_invariant hseed.2.1 hcascade
  have hhy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + succSchedD D₀ N p (H + 1) - 1)) =
          Rk.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.mpr ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1))) := by
    intro v u γ hu
    rw [show Rk.S = G'.sysS P seedK freshK φ₀ hφ₀ from hS]
    filter_upwards [hyom v u γ hu] with t ht
    have heq := frontier_sysS_parameters_congr G'
      (succProvParams D Cw kI.cr σ₀ (succEta0 α q t) N p) P rfl seedK freshK φ₀ hφ₀
    simpa only [F, heq] using ht
  have hhyom' : ∀ v u (γ : G'.fam.Γ v u) (hu : IsRetained m H J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
        (yom v u γ t).val (valueIndex2 (k + succSchedD D₀ N p (H + 1) - 1)) =
          G'.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q t) N p)
            seedK freshK φ₀ hφ₀ v u γ t
              ((Yw ⟨u.1, Finset.mem_filter.mpr ⟨u.2, hu⟩⟩ t).val (valueIndex2 (k + 1))) := by
    intro v u γ hu
    filter_upwards [hyom v u γ hu] with t ht
    have heq := frontier_sysS_parameters_congr G'
      (succProvParams D Cw kI.cr σ₀ (succEta0 α q t) N p) P rfl seedK freshK φ₀ hφ₀
    simpa only [heq] using ht
  have hprices := hprice D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA s₀ htA hdelay hwindow hT
    G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hhyom'
  change ∀ l : ℕ, 1 ≤ l → l ≤ J + 1 → FreshPrefixPriceStatement F l Cp at hprices
  have hrows : WordLengthRowsStatement F Cp :=
    fun l hl hlJ => word_length_row_of_price F l Cp hl hlJ (hprices l hl hlJ) hsol.2.1
  exact length_source_energy_of_extended_operator F hqD hΛD P Mn seedK freshK φ₀ hφ₀
    hactual (fun v hv => (hold v hv).1) hlevel Rk hB hC hS hπ hφ
    αv 1024 (D.eps (m - 1)) hαv (by norm_num) (he _) hsmallD hstrain hjets
    Y Yk hsol htrace.2 hhy Cp hrows (he _)
end

end AVRegularity.Construction.Preservation.Frontier.LengthEnergy
end
end
end
