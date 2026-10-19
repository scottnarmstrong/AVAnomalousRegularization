-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.Construction.Preservation.RetainedEnergy.Producer
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real

section
section
/-! Stage-generic analytic inputs of the frontier estimate. The outside-row flux,
its readout and the source-layer dissipation are estimated separately. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Data shared by the grade and length frontiers; certificates are hypotheses of producers,
not fields hiding any analytic estimate. -/
structure Frame (D : OCData) (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) where
  G : GenStage D hr Dm bw j₀
  G' : GenStage D hr Dm bw j₀
  law : BirthLaw
  m : ℕ
  H : ℕ
  J : ℕ
  k : ℕ
  cr : ℝ
  η : ℝ
  θ₁ : ℝ
  θ₂ : ℝ
  tp : ℝ
  tf : ℝ
  Y0 : ∀ v : CompIn (G'.retained m H J).comps, TorusHk k (hr v.1.root)
  Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (k + 1) (hr v.1.root)
  yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)

abbrev Frame.Gr (F : Frame D hr Dm bw j₀) := F.G'.retained F.m F.H F.J
abbrev Frame.RowFlux (F : Frame D hr Dm bw j₀) :=
  ∀ v : CompIn F.G'.comps, ℝ → TorusHk F.k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))
abbrev Frame.ReadoutFlux (F : Frame D hr Dm bw j₀) :=
  ∀ v : CompIn F.G.comps, ℝ → TorusHk F.k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))

def Frame.select (F : Frame D hr Dm bw j₀) (grade : Bool) (c : Comp) : Prop :=
  if grade then compGrade c = F.H + 1
  else compGrade c ≤ F.H ∧ (compWord F.m c).length = F.J + 1

def Frame.exponent (F : Frame D hr Dm bw j₀) (grade : Bool) : ℝ :=
  if grade then F.η / 8 * succSigmaH D.q F.H else F.θ₁ + F.J * F.θ₂

def Frame.rowGain (F : Frame D hr Dm bw j₀) (grade : Bool) : ℝ :=
  if grade then 1 else D.eps (F.m - 1) ^ (if F.J = 0 then F.θ₁ else F.θ₂)
def Frame.markerGain (F : Frame D hr Dm bw j₀) (grade : Bool) : ℝ :=
  if grade then D.eps (F.m - 1) ^ F.exponent true else 1
def Frame.layerGain (F : Frame D hr Dm bw j₀) (grade : Bool) : ℝ :=
  if grade then 1 else D.eps (F.m - 1) ^
    (if F.J = 0 then 0 else F.θ₁ + (F.J - 1 : ℕ) * F.θ₂)

def Frame.initialNorm (F : Frame D hr Dm bw j₀) : ℝ :=
  weightedNorm (rhoEnh D F.cr F.m) (F.Gr.mass F.law) (F.Gr.marker F.law) F.Y0

def Frame.sourceDissipation (F : Frame D hr Dm bw j₀) (grade : Bool) : ℝ :=
  D.κ (F.m - 1) * ∫ t in Set.Icc F.tp F.tf,
    massGradNormSq (E := fun v : CompIn F.Gr.comps => hr v.1.root) (K := fun _ => F.k)
      (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
      (fun v => if grade || (compWord F.m v.1).length = F.J then (F.Yw v t).val else 0)

def Frame.rowEnergy (F : Frame D hr Dm bw j₀) (OF : F.RowFlux) : ℝ :=
  (D.κ (F.m - 1))⁻¹ * ∫ t in Set.Icc F.tp F.tf,
    massNormSq (E := fun v : CompIn F.G'.comps => PiLp 2 (fun _ : Fin 2 => hr v.1.root))
      (K := fun _ => F.k) (rhoEnh D F.cr F.m)
      (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (OF v t).val)

def Frame.readoutEnergy (F : Frame D hr Dm bw j₀) (RF : F.ReadoutFlux) : ℝ :=
  (D.κ (F.m - 1))⁻¹ * ∫ t in Set.Icc F.tp F.tf,
    massNormSq (E := fun v : CompIn F.G.comps => PiLp 2 (fun _ : Fin 2 => hr v.1.root))
      (K := fun _ => F.k) (rhoEnh D F.cr F.m) (F.G.mass F.law) (fun v => (RF v t).val)

open scoped Classical in
/-- The selected outside-row representative, zero on other rows. -/
def Frame.RealizesRows (F : Frame D hr Dm bw j₀) (grade : Bool) (OF : F.RowFlux) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
    (OF v t).toFunction.jet (valueIndex2 F.k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => if F.select grade v.1 then
        omittedFlux F.G' F.k (IsRetained F.m F.H F.J) F.yom v t x else 0

def Frame.RealizesReadout (F : Frame D hr Dm bw j₀) (grade : Bool)
    (RF : F.ReadoutFlux) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
    (RF v t).toFunction.jet (valueIndex2 F.k) =ᵐ[volume.restrict AVenhance.unitCube]
      readoutFlux F.m (D.eps (F.m - 1)) F.η (F.select grade)
        (omittedFlux F.G' F.k (IsRetained F.m F.H F.J) F.yom) v t

/-- Cauchy on the extended rows and the original kernels, including fresh-prefix prices.
The degenerate cases are included: empty rows give zero; a singleton includes its diagonal letter;
Dm=2 needs only a first derivative. Identity metric, zero data and edgeless seeds retain this same
estimate. -/
def OutsideRowCauchyStatement (F : Frame D hr Dm bw j₀) (grade : Bool) (C : ℝ) : Prop :=
  ∃ OF : F.RowFlux, F.RealizesRows grade OF ∧
    (∀ v, MemLp (OF v) 2 (volume.restrict (Set.Icc F.tp F.tf))) ∧
    F.rowEnergy OF ≤ (C * F.rowGain grade) ^ 2 * F.sourceDissipation grade

open scoped Classical in
/-- One fresh-prefix flux estimate, shared by the interior length blocks and the final
omitted length frontier. The inputs are restricted to lengths at most l-1; actual provenance
forces the contributing fresh columns to have length exactly l-1. Time integrability belongs
here, before applying the forced kernel-energy estimate.
The degenerate cases are included: l=1 is fed by empty words and costs theta1; later prefixes cost
theta2. J=0 has just l=1. Empty and singleton families, k=0, identity metric, zero data and an
edgeless seed require no division. -/
def WordLengthRowStatement (F : Frame D hr Dm bw j₀) (l : ℕ) (C : ℝ) : Prop :=
  ∃ OF : F.RowFlux,
    (∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      (OF v t).toFunction.jet (valueIndex2 F.k) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => if compGrade v.1 ≤ F.H ∧ (compWord F.m v.1).length = l then
          omittedFlux F.G' F.k (IsRetained F.m F.H (l - 1)) F.yom v t x else 0) ∧
    (∀ v, MemLp (OF v) 2 (volume.restrict (Set.Icc F.tp F.tf))) ∧
    F.rowEnergy OF ≤
      (C * D.eps (F.m - 1) ^ (if l = 1 then F.θ₁ else F.θ₂)) ^ 2 *
        (D.κ (F.m - 1) * ∫ t in Set.Icc F.tp F.tf,
          massGradNormSq (E := fun v : CompIn F.Gr.comps => hr v.1.root) (K := fun _ => F.k)
            (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
            (fun v => if (compWord F.m v.1).length = l - 1 then (F.Yw v t).val else 0))

/-- The same row producer is used at every prefix, including the final omitted row.
The degenerate cases are included: the range is 1..J+1, never empty; J=0 has no interior forced
layer. -/
def WordLengthRowsStatement (F : Frame D hr Dm bw j₀) (C : ℝ) : Prop :=
  ∀ l : ℕ, 1 ≤ l → l ≤ F.J + 1 → WordLengthRowStatement F l C

/-- The readout estimate on arbitrary selected fluxes. Grade H+1 supplies the
marker gain; length uses the fresh mass ratios and the bounded readout action.
The norm estimate is pointwise; time integrability is proved by the row producer.
The degenerate cases are included: J=0 is the first prefix; empty sums vanish; one component and
identity metric are allowed; no new edge is assumed of an edgeless seed. -/
def MarkerReadoutStatement (F : Frame D hr Dm bw j₀) (grade : Bool) (C : ℝ) : Prop :=
  ∀ OF : F.RowFlux, F.RealizesRows grade OF →
    (∀ v, MemLp (OF v) 2 (volume.restrict (Set.Icc F.tp F.tf))) →
    ∃ RF : F.ReadoutFlux, F.RealizesReadout grade RF ∧
      (∀ v, MemLp (RF v) 2 (volume.restrict (Set.Icc F.tp F.tf))) ∧
      ∀ t ∈ Set.Icc F.tp F.tf,
        massNormSq (rhoEnh D F.cr F.m) (F.G.mass F.law) (fun v => (RF v t).val) ≤
          (C * F.markerGain grade) ^ 2 *
            massNormSq (rhoEnh D F.cr F.m)
              (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
              (fun v => (OF v t).val)

/-- Grade: marked homogeneous contraction. Length: forced energy on the copied
word blocks, whose non-root traces vanish; the first prefix costs theta1, later ones theta2.
The degenerate cases are included: J=0 reduces to homogeneous contraction, not a positive-length
recurrence; empty and singleton families and Ain=0 are covered without dividing by their norms. -/
def SourceLayerEnergyStatement (F : Frame D hr Dm bw j₀) (grade : Bool) (C : ℝ) : Prop :=
  F.sourceDissipation grade ≤ (C * F.layerGain grade * F.initialNorm) ^ 2

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! The grade frontier uses the already proved retained marked contraction. Covariance
trace uniqueness allows its estimate to be used with an arbitrary trace witness. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier
open FullLift AVRegularity.CoupledEnergy.Variational
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Every literal retained trace is the trace constructed by prepared energy.
The degenerate cases are included: empty families are vacuous, and new components have exactly zero
trace. -/
theorem frontier_retained_trace_unique (G Gr : GenStage D hr Dm bw j₀)
    {m p k n : ℕ} {tp : ℝ}
    (f : ∀ v : CompIn G.comps, TorusHk n (hr v.1.root))
    (Y0 Y1 : ∀ v : CompIn Gr.comps, TorusHk k (hr v.1.root))
    (h0 : IsRetainedTrace G Gr m p tp f Y0) (h1 : IsRetainedTrace G Gr m p tp f Y1) : Y0 = Y1 := by
  classical
  funext v
  by_cases hv : v.1 ∈ G.comps
  · exact covImage_unique _ _ _ _ (h0.1 v hv) (h1.1 v hv)
  · rw [h0.2 v hv, h1.2 v hv]

/-- The grade source budget is a consequence of the marked contraction, not another frontier
estimate. Empty, singleton and edgeless stages and k=0 use exactly the same argument. -/
theorem grade_source_energy_of_retained_solution (F : Frame D hr Dm bw j₀)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hν : 0 ≤ D.κ (F.m - 1)) (ht : F.tp ≤ F.tf)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (C Q Ain : ℝ)
    (hc : RetainedSolutionClauses F.law P seedK freshK φ₀ hφ₀ F.Gr F.m F.k F.cr C Q Ain F.tp F.tf F.Y0)
    (Y : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk F.k (hr v.1.root))
    (Yk : ∀ v u (_ : F.Gr.fam.Γ v u), ℝ → TorusHk (F.k + Dm - 1) (hr u.1.root))
    (hsol : F.Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (F.m - 1))
      (streamVel (D.Φ (F.m - 1))) F.k F.tp F.tf F.Y0 (fun _ _ => 0) (fun _ _ => 0) Y F.Yw Yk) :
    SourceLayerEnergyStatement F true 1 := by
  classical
  let I := ∫ t in Set.Icc F.tp F.tf,
    massGradNormSq (E := fun v : CompIn F.Gr.comps => hr v.1.root) (K := fun _ => F.k)
      (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
      (fun v => (F.Yw v t).val)
  have hI : 0 ≤ I := integral_nonneg fun t => massGradNormSq_nonneg _ _
    (fun (v : CompIn F.Gr.comps) => div_pos (Buffer.birth_compMass_pos hq hΛ F.law v.1)
      (sq_pos_of_pos (Buffer.birth_compMarker_pos hq hΛ F.law v.1))) _
  have he := (hc.2 Y Y F.Yw F.Yw Yk Yk hsol hsol).2 (F.Gr.marker F.law) (Or.inr rfl)
    F.tf ⟨ht, le_rfl⟩
  have he' : weightedNorm (rhoEnh D F.cr F.m) (F.Gr.mass F.law) (F.Gr.marker F.law)
      (fun v => Y v F.tf) ^ 2 + 5 * D.κ (F.m - 1) / 4 * I ≤ F.initialNorm ^ 2 := he.1
  have hdrop : D.κ (F.m - 1) * I ≤ F.initialNorm ^ 2 := by
    have hi := mul_nonneg hν hI
    have hn := sq_nonneg (weightedNorm (rhoEnh D F.cr F.m) (F.Gr.mass F.law)
      (F.Gr.marker F.law) (fun v => Y v F.tf))
    linarith only [he', hi, hn]
  simpa only [SourceLayerEnergyStatement, Frame.sourceDissipation, Frame.layerGain,
    ite_true, Bool.true_or, one_mul] using hdrop

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! The analytic frontier factors compose without component counts or loss in exponents. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem frontier_gain_product (F : Frame D hr Dm bw j₀) (hE : 0 < D.eps (F.m - 1))
    (grade : Bool) :
    F.rowGain grade * F.markerGain grade * F.layerGain grade =
      D.eps (F.m - 1) ^ F.exponent grade := by
  cases grade with
  | true => simp only [Frame.rowGain, Frame.markerGain, Frame.layerGain, ite_true, one_mul, mul_one]
  | false =>
    by_cases hJ : F.J = 0
    · simp only [Frame.rowGain, Frame.markerGain, Frame.layerGain, Frame.exponent,
        hJ, ite_eq_left, Bool.false_eq_true, ite_false, Nat.cast_zero, zero_mul, add_zero,
        mul_one, Real.rpow_zero]
    · have hcast : (F.J : ℝ) = (F.J - 1 : ℕ) + 1 := by
        exact_mod_cast (show F.J = F.J - 1 + 1 by omega)
      simp only [Frame.rowGain, Frame.markerGain, Frame.layerGain, Frame.exponent,
        hJ, ite_false, Bool.false_eq_true, mul_one]
      rw [← Real.rpow_add hE]
      congr 1
      rw [hcast]
      ring

/-- The last instance of the common prefix estimate is precisely the omitted length row.
The degenerate cases are included: at J=0 this is the first-prefix estimate with theta1, without a
recurrence. -/
theorem outside_length_rows_of_prefix_rows (F : Frame D hr Dm bw j₀) (C : ℝ)
    (h : WordLengthRowsStatement F C) : OutsideRowCauchyStatement F false C := by
  obtain ⟨OF, hOF, hLp, hb⟩ := h (F.J + 1) (by omega) le_rfl
  refine ⟨OF, ?_, hLp, ?_⟩
  · simpa only [Frame.RealizesRows, Frame.select, Bool.false_eq_true, ite_false,
      Nat.add_sub_cancel] using hOF
  · have he : F.J + 1 = 1 ↔ F.J = 0 := by omega
    simpa only [Frame.rowGain, Frame.sourceDissipation, Bool.false_eq_true, ite_false,
      Bool.false_or, Nat.add_sub_cancel, he, decide_eq_true_eq] using hb

/-- Three genuinely separate estimates give the frontier conclusion at one fixed stage.
The degenerate cases are included: empty families, J=0, order zero and zero initial norm require no
cancellation or division by data. The constants are polynomially combined and may have either sign.
-/
theorem frontier_at_stage_of_analytic_inputs (F : Frame D hr Dm bw j₀)
    (hE : 0 < D.eps (F.m - 1)) (hν : 0 ≤ D.κ (F.m - 1)) (grade : Bool) (C : ℝ)
    (hrows : OutsideRowCauchyStatement F grade C)
    (hread : MarkerReadoutStatement F grade C)
    (hsource : SourceLayerEnergyStatement F grade C) :
    ∃ RF : F.ReadoutFlux, F.RealizesReadout grade RF ∧
      F.readoutEnergy RF ≤ (C ^ 3 * D.eps (F.m - 1) ^ F.exponent grade * F.initialNorm) ^ 2 := by
  obtain ⟨OF, hOF, hOFlp, hrow⟩ := hrows
  obtain ⟨RF, hRF, hRFlp, hpoint⟩ := hread OF hOF hOFlp
  have hRi := CycleComparison.Error.integrable_massNormSq
    (rhoEnh D F.cr F.m) (F.G.mass F.law) RF hRFlp
  have hOi := CycleComparison.Error.integrable_massNormSq
    (rhoEnh D F.cr F.m)
    (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) OF hOFlp
  have hi := integral_mono_ae hRi (hOi.const_mul ((C * F.markerGain grade) ^ 2))
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hpoint t ht)
  have hR : F.readoutEnergy RF ≤ (C * F.markerGain grade) ^ 2 * F.rowEnergy OF := by
    dsimp only [Frame.readoutEnergy, Frame.rowEnergy]
    rw [integral_const_mul] at hi
    exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hν)).trans_eq (by ring)
  refine ⟨RF, hRF, hR.trans ?_⟩
  calc
    (C * F.markerGain grade) ^ 2 * F.rowEnergy OF ≤
        (C * F.markerGain grade) ^ 2 * ((C * F.rowGain grade) ^ 2 * F.sourceDissipation grade) :=
      mul_le_mul_of_nonneg_left hrow (sq_nonneg _)
    _ ≤ (C * F.markerGain grade) ^ 2 *
        ((C * F.rowGain grade) ^ 2 * (C * F.layerGain grade * F.initialNorm) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsource (sq_nonneg _)) (sq_nonneg _)
    _ = (C ^ 3 * (F.rowGain grade * F.markerGain grade * F.layerGain grade) * F.initialNorm) ^ 2 := by ring
    _ = _ := by rw [frontier_gain_product F hE grade]

end AVRegularity.Construction.Preservation.Frontier
end
end
end

section
section
/-! Uniform data-level statements for the three analytic frontier inputs. Unlike a split
by discarded-row cases, these expose the different operators and energy mechanisms. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier
open AVRegularity.Construction.Preservation.Assembly

/-- The certificates, row witnesses and solutions instantiate the three stage-generic estimates.
No hard estimate is assumed as a certificate. -/
def FrontierAnalyticProductionDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C : ℝ) (mStar : ℕ) (grade : Bool)
    (join : Prop → Prop → Prop → Prop := fun rows readout source => rows ∧ readout ∧ source) : Prop :=
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
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ k ≤ Kres,
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk k (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk k (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) k tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root),
      (∀ v u (γ : G'.fam.Γ v u) (hu : IsRetained m H J u.1),
        ∀ᵐ t ∂(volume.restrict (Set.Icc tp tf)),
          (yom v u γ t).val (valueIndex2 (k + succSchedD D₀ N p (H + 1) - 1)) =
            G'.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q t) N p) seedK freshK φ₀ hφ₀ v u γ t
              ((Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val (valueIndex2 (k + 1)))) →
    let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
      { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
        cr := kI.cr, η := succEta0 α q s,
        θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
        θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
        tp := tp, tf := tf, Y0 := Y0, Yw := Yw, yom := yom }
    join (OutsideRowCauchyStatement F grade C) (MarkerReadoutStatement F grade C)
      (SourceLayerEnergyStatement F grade C)

def FrontierAnalyticProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ) (grade : Bool)
    (join : Prop → Prop → Prop → Prop := fun rows readout source => rows ∧ readout ∧ source) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C : ℝ) (mStar : ℕ),
    FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar grade join

/-- Exact uniform frontier conclusion from the analytic decomposition. The remaining producer
must supply one common C and threshold for its row, readout and source-layer estimates. -/
theorem frontier_production_of_analytic_inputs (α s q : ℝ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (grade : Bool)
    (h : FrontierAnalyticProductionStatement α s q ζ grade) :
    FrontierProductionStatement α s q ζ grade := by
  classical
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, h⟩ := h Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, h⟩ := h kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨C, mStar, h⟩ := h CI Cw j₀ hledger hstart CQ Cpr
  refine ⟨C ^ 3, mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hyom sel expo hsel
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
      cr := kI.cr, η := succEta0 α q s,
      θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
      θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
      tp := tp, tf := tf, Y0 := Y0, Yw := Yw, yom := yom }
  have hinputs : OutsideRowCauchyStatement F grade C ∧ MarkerReadoutStatement F grade C ∧
      SourceLayerEnergyStatement F grade C := h D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hdelay hwindow hT
    G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hyom
  have hE : 0 < D.eps (m - 1) := Construction.Stream.ocEpsilon_pos (by rw [hDΛ]; omega)
  have hsel' : sel = F.select grade := by
    cases grade <;> exact hsel.1
  have hexpo : expo = F.exponent grade := by
    cases grade <;> simpa only [F, Frame.exponent, Bool.false_eq_true, ite_false, ite_true, hDq] using hsel.2
  rw [hsel', hexpo]
  have hν : 0 ≤ D.κ (m - 1) :=
    (CycleReference.bandChain_pos (by omega : 1 ≤ Λ) hζ hband (show m - 1 ≤ M by omega)).le
  exact frontier_at_stage_of_analytic_inputs F hE hν grade C hinputs.1 hinputs.2.1 hinputs.2.2

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! Combiner for the three single-component frontier productions. The data-level part
(`frontier_data_and`) merges the constants of the three estimates; the outer statement
(`frontier_analytic_production_and`) merges thresholds, one lemma per constant. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier
open AVRegularity.Construction.Preservation.Assembly

section Mono
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Absorb a signed constant into a larger one, without a sign condition on the factor. -/
theorem sq_budget_of_abs_le {a C x : ℝ} (h : |a| ≤ C) : (a * x) ^ 2 ≤ (C * x) ^ 2 := by
  rw [mul_pow, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← sq_abs a]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

theorem Frame.mass_ratio_pos (F : Frame D hr Dm bw j₀) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) :
    ∀ v, 0 < F.G'.mass F.law v / F.G'.marker F.law v ^ 2 := fun v =>
  div_pos (Buffer.birth_compMass_pos hq hΛ F.law v.1)
    (pow_pos (Buffer.birth_compMarker_pos hq hΛ F.law v.1) 2)

theorem Frame.mass_ratio_pos_retained (F : Frame D hr Dm bw j₀) (hq : 1 < D.q)
    (hΛ : 128 ≤ D.Λ) :
    ∀ v, 0 < F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2 := fun v =>
  div_pos (Buffer.birth_compMass_pos hq hΛ F.law v.1)
    (pow_pos (Buffer.birth_compMarker_pos hq hΛ F.law v.1) 2)

theorem Frame.sourceDissipation_nonneg (F : Frame D hr Dm bw j₀) (grade : Bool)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hν : 0 ≤ D.κ (F.m - 1)) :
    0 ≤ F.sourceDissipation grade :=
  mul_nonneg hν (integral_nonneg fun _ =>
    CoupledEnergy.Variational.massGradNormSq_nonneg _ _ (F.mass_ratio_pos_retained hq hΛ) _)

theorem OutsideRowCauchyStatement.mono (F : Frame D hr Dm bw j₀) (grade : Bool) {Ca C : ℝ}
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hν : 0 ≤ D.κ (F.m - 1)) (hC : |Ca| ≤ C)
    (h : OutsideRowCauchyStatement F grade Ca) : OutsideRowCauchyStatement F grade C := by
  obtain ⟨OF, hOF, hLp, hb⟩ := h
  exact ⟨OF, hOF, hLp, hb.trans (mul_le_mul_of_nonneg_right (sq_budget_of_abs_le hC)
    (F.sourceDissipation_nonneg grade hq hΛ hν))⟩

theorem MarkerReadoutStatement.mono (F : Frame D hr Dm bw j₀) (grade : Bool) {Ca C : ℝ}
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hC : |Ca| ≤ C)
    (h : MarkerReadoutStatement F grade Ca) : MarkerReadoutStatement F grade C := by
  intro OF hOF hLp
  obtain ⟨RF, hRF, hRLp, hb⟩ := h OF hOF hLp
  refine ⟨RF, hRF, hRLp, fun t ht => (hb t ht).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (sq_budget_of_abs_le hC)
    (CoupledEnergy.Variational.massNormSq_nonneg _ _ (F.mass_ratio_pos hq hΛ) _)

theorem SourceLayerEnergyStatement.mono (F : Frame D hr Dm bw j₀) (grade : Bool) {Ca C : ℝ}
    (hC : |Ca| ≤ C) (h : SourceLayerEnergyStatement F grade Ca) :
    SourceLayerEnergyStatement F grade C := by
  have := sq_budget_of_abs_le (x := F.layerGain grade * F.initialNorm) hC
  rw [← mul_assoc, ← mul_assoc] at this
  exact h.trans this

end Mono

/-- Data-level merge: three estimates with constants `C₁ C₂ C₃` and thresholds `m₁ m₂ m₃`
give the default conjunction with any `C` dominating the absolute values. -/
theorem frontier_data_and (α s q : ℝ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hq1 : 1 < q)
    (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (grade : Bool)
    (C₁ C₂ C₃ C : ℝ) (m₁ m₂ m₃ mStar : ℕ)
    (h₁ : |C₁| ≤ C) (h₂ : |C₂| ≤ C) (h₃ : |C₃| ≤ C)
    (g₁ : m₁ ≤ mStar) (g₂ : m₂ ≤ mStar) (g₃ : m₃ ≤ mStar)
    (d₁ : FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C₁ m₁ grade
      (fun rows _ _ => rows))
    (d₂ : FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C₂ m₂ grade
      (fun _ r _ => r))
    (d₃ : FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C₃ m₃ grade
      (fun _ _ s => s)) :
    FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar grade := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom hyom F
  have hqD : 1 < D.q := hDq.symm ▸ hq1
  have hΛD : 128 ≤ D.Λ := hDΛ.symm ▸ hΛ
  have hν : 0 ≤ D.κ (m - 1) :=
    (CycleReference.bandChain_pos (le_trans (by norm_num) hΛ) hζ hband
      ((Nat.sub_le m 1).trans (hn.trans hnM.le))).le
  have e₁ : OutsideRowCauchyStatement F grade C₁ := d₁ D hDα hDq hDΛ hDζ hseq M hband hterm Mnat
    hMnat law hlaw seedK freshK hfresh seed n tS tf hseed m (g₁.trans hm) hn hnM tA s₀ htA hdelay
    hwindow hT G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol
    yom hyom
  have e₂ : MarkerReadoutStatement F grade C₂ := d₂ D hDα hDq hDΛ hDζ hseq M hband hterm Mnat
    hMnat law hlaw seedK freshK hfresh seed n tS tf hseed m (g₂.trans hm) hn hnM tA s₀ htA hdelay
    hwindow hT G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol
    yom hyom
  have e₃ : SourceLayerEnergyStatement F grade C₃ := d₃ D hDα hDq hDΛ hDζ hseq M hband hterm Mnat
    hMnat law hlaw seedK freshK hfresh seed n tS tf hseed m (g₃.trans hm) hn hnM tA s₀ htA hdelay
    hwindow hT G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol
    yom hyom
  exact ⟨e₁.mono F grade hqD hΛD hν h₁, e₂.mono F grade hqD hΛD h₂, e₃.mono F grade h₃⟩

/-- Common nonnegativity of the carrier-start amplitudes. -/
theorem carrier_start_amplitudes_nonneg {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    (∀ i, 0 ≤ ocA α q Λ i) ∧ ∀ i, 0 ≤ ocTauPP α q Λ i :=
  ⟨fun _ => (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ) _).le,
    fun _ => (Construction.Stream.ocTauPP_pos hΛ).le⟩

/-- Ledger admissibility is monotone in both thresholds. -/
theorem ledgerAdmissible_weaken {Ce CI Cw a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b')
    (h : IsLedgerAdmissible Ce CI Cw a' b') : IsLedgerAdmissible Ce CI Cw a b :=
  ⟨h.1, ha.trans h.2.1, hb.trans h.2.2.1, h.2.2.2⟩

/-- The default-join frontier production from the three single-component productions. -/
theorem frontier_analytic_production_and (α s q : ℝ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hq1 : 1 < q) (grade : Bool)
    (h₁ : FrontierAnalyticProductionStatement α s q ζ grade (fun rows _ _ => rows))
    (h₂ : FrontierAnalyticProductionStatement α s q ζ grade (fun _ r _ => r))
    (h₃ : FrontierAnalyticProductionStatement α s q ζ grade (fun _ _ s => s)) :
    FrontierAnalyticProductionStatement α s q ζ grade := by
  classical
  obtain ⟨Λ₁, hΛ₁, h₁⟩ := h₁
  obtain ⟨Λ₂, hΛ₂, h₂⟩ := h₂
  obtain ⟨Λ₃, hΛ₃, h₃⟩ := h₃
  refine ⟨max Λ₁ (max Λ₂ Λ₃), by omega, ?_⟩
  intro Λ hΛ
  have hΛ128 : 128 ≤ Λ := by omega
  obtain ⟨c₁, hc₁, h₁⟩ := h₁ Λ (by omega)
  obtain ⟨c₂, hc₂, h₂⟩ := h₂ Λ (by omega)
  obtain ⟨c₃, hc₃, h₃⟩ := h₃ Λ (by omega)
  refine ⟨min c₁ (min c₂ c₃), lt_min hc₁ (lt_min hc₂ hc₃), ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨t₁, CH₁, Υ₁, hCH₁, hΥ₁, h₁⟩ := h₁ φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  obtain ⟨t₂, CH₂, Υ₂, hCH₂, hΥ₂, h₂⟩ := h₂ φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans ((min_le_right _ _).trans (min_le_left _ _))) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  obtain ⟨t₃, CH₃, Υ₃, hCH₃, hΥ₃, h₃⟩ := h₃ φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans ((min_le_right _ _).trans (min_le_right _ _))) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  refine ⟨certificateThresholdJoin t₁ (certificateThresholdJoin t₂ t₃),
    max CH₁ (max CH₂ CH₃), max Υ₁ (max Υ₂ Υ₃), hCH₁.trans (le_max_left _ _),
    hΥ₁.trans_le (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CI₁, Cw₁, h₁⟩ := h₁ kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CI₂, Cw₂, h₂⟩ := h₂ kI
    (invariant_admissible_threshold_left (invariant_admissible_threshold_right hkI))
  obtain ⟨CI₃, Cw₃, h₃⟩ := h₃ kI
    (invariant_admissible_threshold_right (invariant_admissible_threshold_right hkI))
  refine ⟨max CI₁ (max CI₂ CI₃), max Cw₁ (max Cw₂ Cw₃), ?_⟩
  intro CI Cw j₀ hledger hstart
  have hL₁ : IsLedgerAdmissible Ce CI Cw CI₁ Cw₁ :=
    ledgerAdmissible_weaken (le_max_left _ _) (le_max_left _ _) hledger
  have hL₂ : IsLedgerAdmissible Ce CI Cw CI₂ Cw₂ :=
    ledgerAdmissible_weaken ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)) hledger
  have hL₃ : IsLedgerAdmissible Ce CI Cw CI₃ Cw₃ :=
    ledgerAdmissible_weaken ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) hledger
  obtain ⟨hA, hT⟩ := carrier_start_amplitudes_nonneg (α := α) (q := q) (by omega : 1 ≤ Λ)
  intro CQ Cpr
  obtain ⟨C₁, m₁, h₁⟩ := h₁ CI Cw j₀ hL₁ (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH₁) hΥ₁.le hstart) CQ Cpr
  obtain ⟨C₂, m₂, h₂⟩ := h₂ CI Cw j₀ hL₂ (IsCarrierStart.mono hA hT
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    (zero_le_one.trans hCH₂) hΥ₂.le hstart) CQ Cpr
  obtain ⟨C₃, m₃, h₃⟩ := h₃ CI Cw j₀ hL₃ (IsCarrierStart.mono hA hT
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    (zero_le_one.trans hCH₃) hΥ₃.le hstart) CQ Cpr
  refine ⟨|C₁| + |C₂| + |C₃| + 1, max m₁ (max m₂ m₃), ?_⟩
  exact frontier_data_and α s q ζ hζ hq1 Λ hΛ128 φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
    Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ grade C₁ C₂ C₃ _ m₁ m₂ m₃ _
    (by linarith [abs_nonneg C₂, abs_nonneg C₃]) (by linarith [abs_nonneg C₁, abs_nonneg C₃])
    (by linarith [abs_nonneg C₁, abs_nonneg C₂])
    (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _)) h₁ h₂ h₃

end AVRegularity.Construction.Preservation.Frontier
end
end

section
/-! Uniform grade-source production from the retained homogeneous contraction. The
uniform prefix is shared with the row and marker estimates; this proof does not use
the held length-source or outside-row statements.

The degenerate cases are included: identity metric, k=0, one or empty component family and an
edgeless seed use the same constant one. The initial norm is never divided out. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier
open AVRegularity.Construction.Preservation.Assembly RetainedEnergy

/-- The grade source estimate with thresholds chosen before the stage and its solution. -/
theorem grade_source_energy_production {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    FrontierAnalyticProductionStatement α s q ζ true (fun _rows _readout source => source) := by
  classical
  obtain ⟨Λ₀, hΛ₀, he⟩ := prepared_retained_energy_production hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, he⟩ := he Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, he⟩ := he φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ r₀ D₀ τe kS.lamC kS.σf hτe hlamC hσf
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux hNout
    sX sZ hsX hsZ Ce kS hCe hc₀ hc₀upper hcr hcrupper rfl rfl halloc
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, he⟩ := he kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨C, ms, he⟩ := he CI Cw j₀ hledger hstart CQ Cpr
  refine ⟨1, ms, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hf k hk Y0 Y Yw Yk htrace hsol yom _hyom
  obtain ⟨_hnext, henergy⟩ := he D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hdelay hwindow hT
    G G' hcascade hlevel hG hactual tp Preg hprep
  obtain ⟨Y1, htrace1, hc⟩ := henergy f Ain hf k hk
  have heq := frontier_retained_trace_unique G (G'.retained m H J) (Preg f) Y0 Y1 htrace htrace1
  rw [← heq] at hc
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
      cr := kI.cr, η := succEta0 α q s,
      θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
      θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
      tp := tp, tf := tf, Y0 := Y0, Yw := Yw, yom := yom }
  have hqD : 1 < D.q := hDq.symm ▸ hq.1
  have h128 : 128 ≤ D.Λ := by rw [hDΛ]; omega
  have hν : 0 ≤ D.κ (m - 1) :=
    (CycleReference.bandChain_pos (by omega : 1 ≤ Λ) hζ hband (show m - 1 ≤ M by omega)).le
  have ht : tp ≤ tf := by
    have hh := hprep.2.2.1
    rw [hlevel, hDα, hDq, hDΛ] at hh
    exact hh.trans hwindow
  exact grade_source_energy_of_retained_solution F hqD h128 hν ht
    (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
    C Q Ain hc Y Yk hsol

end AVRegularity.Construction.Preservation.Frontier
end
end
end
