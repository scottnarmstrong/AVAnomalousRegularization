-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.AmplitudeIdPeriodizedValue
public import AVRegularity.CycleJoint.PeriodizedCarrierRawReadout
public import AVRegularity.CycleWords.Assembly.MixedWordsB1ZeroWord
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleJoint.TransitionAffineSampling
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # The stage index, its order, the rescaling and the stage curves

A stage is `i = (j, x, β, e)`: a level `j`, a component `x`, a moment `β` with
`|β| ≤ n_j = m + ∑_{l ≥ j} K_s(l)` (`b1wLevelMoments`), and a vector `e` of the standard orthonormal
basis of `h x`. The letter `l` maps level `l` to level `l + 1` and spends at most `K_s(l)` moments,
so the source of `(j + 1, β)` involves level `j` with moments `≤ |β| + K_s(j)` and lower moments of
level `j + 1`. Hence the order is by the degree `|β| + ∑_{l < j} K_s(l)` (`b1wPrefix`), then by
level (`b1wSt`). With it the stages up to the output `out β` (level `N_w`, degree `|β|`) see only
level-0 moments `≤ |β| + ∑ K_s` (`b1wSt_level_zero`), as `datumJets` of the word fibre facts asks.

The stage value is `π_x^{-1/2} ϖ^{|β|}/β! · A_j⁻¹` (`b1wScale`) times the cell solution of the
amplitude identification, where `A_j = ∏_{l<j} θ_l (η_g if positive)` (`b1wAmp`, `A_{N_w}` =
`wordTheta`). `b1w_stage_curves` gives these curves as Hilbert curves of the actual fibre
coefficients `⟨G, v, √η ξ, 0⟩` from the measurable fibre clause of the amplitude identification. -/

universe u v

/-- The moment reserve of level `j`: `n_j = m + ∑_{l ≥ j} K_s(l)`. -/
def b1wLevelMoments {Nw : ℕ} (m : ℕ) (Ks : Fin Nw → ℕ) (j : Fin (Nw + 1)) : ℕ :=
  m + ∑ l : Fin Nw, if j.val ≤ l.val then Ks l else 0

/-- The slow orders spent before level `j`: `∑_{l < j} K_s(l)`. -/
def b1wPrefix {Nw : ℕ} (Ks : Fin Nw → ℕ) (j : Fin (Nw + 1)) : ℕ :=
  ∑ l : Fin Nw, if l.val < j.val then Ks l else 0

theorem b1wPrefix_add_levelMoments {Nw : ℕ} (m : ℕ) (Ks : Fin Nw → ℕ) (j : Fin (Nw + 1)) :
    b1wPrefix Ks j + b1wLevelMoments m Ks j = m + ∑ l, Ks l := by
  unfold b1wPrefix b1wLevelMoments
  rw [add_left_comm, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
  split_ifs <;> omega

theorem b1wPrefix_zero {Nw : ℕ} (Ks : Fin Nw → ℕ) : b1wPrefix Ks 0 = 0 := by
  unfold b1wPrefix
  exact Finset.sum_eq_zero fun l _ => by simp

/-- The stage index: level, component, moment, basis vector. -/
abbrev B1WIndex (ι : Type u) (h : ι → Type v) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] (Nw m : ℕ) (Ks : Fin Nw → ℕ) : Type u :=
  Σ j : Fin (Nw + 1), Σ x : ι,
    {β : ℕ × ℕ // β ∈ momentIndices (b1wLevelMoments m Ks j)} × Fin (Module.finrank ℝ (h x))

section Index

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The degree of a stage, `|β| + ∑_{l < j} K_s(l)`. -/
def b1wDeg (i : B1WIndex ι h Nw m Ks) : ℕ :=
  i.2.2.1.1.1 + i.2.2.1.1.2 + b1wPrefix Ks i.1

/-- The stage order: by degree, then by level. -/
def b1wSt (i : B1WIndex ι h Nw m Ks) : ℕ := b1wDeg i * (Nw + 1) + i.1.val

/-- The number of stages. -/
def b1wM (Nw m : ℕ) (Ks : Fin Nw → ℕ) : ℕ := (m + ∑ l, Ks l + 1) * (Nw + 1)

/-- The output stage of the moment `β`: level `N_w`, degree `|β| + ∑ K_s`. -/
def b1wOut (Nw : ℕ) (Ks : Fin Nw → ℕ) (β : ℕ × ℕ) : ℕ := (β.1 + β.2 + ∑ l, Ks l) * (Nw + 1) + Nw

theorem b1wDeg_le (i : B1WIndex ι h Nw m Ks) : b1wDeg i ≤ m + ∑ l, Ks l := by
  have hβ := (Finset.mem_filter.1 i.2.2.1.2).2
  have he := b1wPrefix_add_levelMoments m Ks i.1
  unfold b1wDeg
  omega

theorem b1wSt_lt (i : B1WIndex ι h Nw m Ks) : b1wSt i < b1wM Nw m Ks := by
  unfold b1wSt b1wM
  have hj := i.1.isLt
  calc b1wDeg i * (Nw + 1) + i.1.val < b1wDeg i * (Nw + 1) + (Nw + 1) := by omega
    _ = (b1wDeg i + 1) * (Nw + 1) := by ring
    _ ≤ (m + ∑ l, Ks l + 1) * (Nw + 1) :=
        Nat.mul_le_mul_right _ (by have := b1wDeg_le i; omega)

theorem b1wOut_lt {β : ℕ × ℕ} (hβ : β ∈ momentIndices m) : b1wOut Nw Ks β < b1wM Nw m Ks := by
  have hb := (Finset.mem_filter.1 hβ).2
  unfold b1wOut b1wM
  calc (β.1 + β.2 + ∑ l, Ks l) * (Nw + 1) + Nw < (β.1 + β.2 + ∑ l, Ks l) * (Nw + 1) + (Nw + 1) :=
        by omega
    _ = (β.1 + β.2 + ∑ l, Ks l + 1) * (Nw + 1) := by ring
    _ ≤ (m + ∑ l, Ks l + 1) * (Nw + 1) := Nat.mul_le_mul_right _ (by omega)

/-- Quotient and remainder by `n` are unique. -/
theorem nat_mul_add_inj {a r a' r' n : ℕ} (hr : r < n) (hr' : r' < n)
    (h : a * n + r = a' * n + r') : a = a' ∧ r = r' := by
  have hn : 0 < n := by omega
  have h1 : (a * n + r) / n = a ∧ (a * n + r) % n = r :=
    (Nat.div_mod_unique hn).2 ⟨by ring, hr⟩
  have h2 : (a' * n + r') / n = a' ∧ (a' * n + r') % n = r' :=
    (Nat.div_mod_unique hn).2 ⟨by ring, hr'⟩
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

/-- **The output stage** is the last level at degree `|β| + ∑ K_s`. -/
theorem b1wSt_eq_out_iff (i : B1WIndex ι h Nw m Ks) (β : ℕ × ℕ) :
    b1wSt i = b1wOut Nw Ks β ↔
      i.1 = Fin.last Nw ∧ i.2.2.1.1.1 + i.2.2.1.1.2 = β.1 + β.2 := by
  unfold b1wSt b1wOut
  constructor
  · intro he
    obtain ⟨hd, hj⟩ := nat_mul_add_inj i.1.isLt (Nat.lt_succ_self Nw) he
    have hl : i.1 = Fin.last Nw := Fin.ext hj
    refine ⟨hl, ?_⟩
    have hp : b1wPrefix Ks i.1 = ∑ l, Ks l := by
      rw [hl]
      unfold b1wPrefix
      exact Finset.sum_congr rfl fun l _ => by simp [l.isLt]
    unfold b1wDeg at hd
    omega
  · rintro ⟨hl, hβ⟩
    have hp : b1wPrefix Ks i.1 = ∑ l, Ks l := by
      rw [hl]
      unfold b1wPrefix
      exact Finset.sum_congr rfl fun l _ => by simp [l.isLt]
    have hv : i.1.val = Nw := by rw [hl, Fin.val_last]
    unfold b1wDeg
    rw [hp, hβ, hv]

end Index

section Scale

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The letter amplitude before level `j`: `A_j = ∏_{l<j} θ_l (η_g if positive)`. -/
def b1wAmp (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (j : Fin (Nw + 1)) : ℝ :=
  ∏ l : Fin Nw, if l.val < j.val then
    (letters l).theta * (if (letters l).positive then ηg else 1) else 1

theorem b1wAmp_last (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) :
    b1wAmp ηg letters (Fin.last Nw) = wordTheta ηg letters := by
  unfold b1wAmp wordTheta
  exact Finset.prod_congr rfl fun l _ => by simp [l.isLt]

/-- The stage rescaling `π_x^{-1/2} ϖ^{|β|}/β! · A_j⁻¹`. -/
def b1wScale (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (i : B1WIndex ι h Nw m Ks) : ℂ :=
  ((π i.2.1 ^ (-(1 / 2 : ℝ)) * ϖ ^ (i.2.2.1.1.1 + i.2.2.1.1.2) /
    ((i.2.2.1.1.1.factorial * i.2.2.1.1.2.factorial : ℕ) : ℝ) *
      (b1wAmp ηg letters i.1)⁻¹ : ℝ) : ℂ)

end Scale


section Curves

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- **The stage curves of the word fibre facts.** From the measurable fibre clause of the
amplitude identification on a frame, every stage `i = (j, x, β, e)` has a cell solution `Dθ i` of
the actual fibre problem, with forcing in `L²` equal slice by slice to the literal forcing of the
amplitude identification, whose value is the Bloch part of `y^β ⟨e, u_j⟩`, and
whose rescaling by any `c i` is a Hilbert curve of `⟨G, v, √η ξ, 0⟩` with the rescaled forcing;
almost every slice of the forcing is in `L²`. -/
theorem b1w_stage_curves {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (θ : Vec 2)
    (hM : ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ),
      ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
        (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
        MemLp (Function.uncurry src) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
        (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
        (∀ᵐ r ∂volume.restrict (Icc F.a F.b),
          src r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ j x e β r ∧
          Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
        IsCellSolution (Icc F.a F.b)
          (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
        ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
          planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)))
    (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (c : B1WIndex ι h Nw m Ks → ℂ) :
    ∃ (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
      (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
      (∀ i, CellWeakHilbertCurve F.a F.b (fun t => cellScalarCLM (c i) (cellRawTrace (Dθ i) t))
        (fun t => cellH1Scalar (c i) (cellH1Slice (Dθ i) t)) (fun t =>
          cellDualDerivative ⟨fun t _ => F.G t, F.v,
            fun k => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ k, 0⟩ F.piece.hGm V
            F.piece.hv.1 hb t (cellH1Scalar (c i) (cellH1Slice (Dθ i) t))
            (cellScalarCLM (c i) (cellSourceSlice (src i) t))
            (fun k => cellScalarCLM (c i) (cellSourceSlice (fun r z => Fl i r z k) t)))) ∧
      (∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
          inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y))) ∧
      (∀ i, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
        src i r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ i.1 i.2.1
          (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1 r ∧
        Fl i r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ i.1 i.2.1
          (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1 r) ∧
      (∀ i, ∀ t ∈ Icc F.a F.b, MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube)) ∧
      ∀ i, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
        MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
          ∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube) := by
  have hstage := fun i : B1WIndex ι h Nw m Ks =>
    hM i.1 i.2.1 (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1
  choose Dθ src Fl hsrc hFl hlit hsol hval using hstage
  refine ⟨Dθ, src, Fl, fun i => ?_, hval, hlit, fun i t ht => ((hsol i).2.2.1 t ht).1,
    fun i => ?_⟩
  swap
  · filter_upwards [cellSource_memLp_slices (Icc F.a F.b) (src i) (hsrc i),
      ae_all_iff.2 fun j : Fin 2 => cellSource_memLp_slices (Icc F.a F.b)
        (fun r z => Fl i r z j) (hFl i j)] with r h1 h2
    exact ⟨h1, h2⟩
  have hs := hsol i
  rw [fibreCoefficients_zero_eq] at hs
  have hH := (cellSolution_to_Hilbert F.ordered ⟨fun t _ => F.G t, F.v,
      fun k => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ k, 0⟩ F.piece.hGm V 0
    F.piece.hv.1 hb measurable_const (fun _ => by simp) (src i) (Fl i) (hsrc i)
    (MemLp.of_eval_piLp (q := 2) fun k => hFl i k) (Dθ i) hs).complex_smul (c i)
  refine CellWeakHilbertCurve.dual_congr hH (Filter.Eventually.of_forall fun t => ?_)
  exact cellDualDerivative_complex_scalar _ F.piece.hGm V F.piece.hv.1 hb t _ _ _ (c i)

end Curves

end AVRegularity.CycleWords.Assembly
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! Every moment-phase of a weighted plane H1 field has a genuine periodic weak jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- A real monomial coordinate, multiplied by the radian phase, retains its fourth radial moment. -/
theorem amplitudeId_scalar_radial_memLp (g : Vec 2 → E)
    (hg : AEStronglyMeasurable g volume) (ϖ : ℝ) (hϖ : 0 < ϖ)
    (hm : ∀ n : ℕ, (∫⁻ y, ENNReal.ofReal
      ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n * ‖g y‖ ^ 2)) < ⊤)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) :
    MemLp (fun y => (1 + ‖y‖) ^ 4 •
      (Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        ((momentWeight β y * inner ℝ e (g y) : ℝ) : ℂ))) 2 volume := by
  have hr := amplitudeId_radial_monomial_memLp g hg ϖ hϖ hm β
  have hc : MemLp (fun y => (1 + ‖y‖) ^ 4 * (momentWeight β y * inner ℝ e (g y))) 2 volume := by
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_smul_right, momentWeight]
      using (innerSL ℝ e).comp_memLp' hr
  convert amplitudeId_phase_memLp θ hc using 1
  funext y
  simp only [Complex.ofReal_mul, Complex.real_smul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The literal monomial gradient is a sum of two lower monomials, also after periodization. -/
theorem amplitudeId_grad_radial_memLp (g : Vec 2 → E)
    (hg : AEStronglyMeasurable g volume) (ϖ : ℝ) (hϖ : 0 < ϖ)
    (hm : ∀ n : ℕ, (∫⁻ y, ENNReal.ofReal
      ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n * ‖g y‖ ^ 2)) < ⊤)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (i : Fin 2) :
    MemLp (fun y => (1 + ‖y‖) ^ 4 •
      (Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        ((momentWeightGrad β y i * inner ℝ e (g y) : ℝ) : ℂ))) 2 volume := by
  fin_cases i
  · convert (amplitudeId_scalar_radial_memLp g hg ϖ hϖ hm θ (β.1 - 1, β.2) e).const_mul (β.1 : ℂ) using 1
    funext y
    simp [momentWeightGrad, momentWeight, Complex.real_smul]
    ring
  · convert (amplitudeId_scalar_radial_memLp g hg ϖ hϖ hm θ (β.1, β.2 - 1) e).const_mul (β.2 : ℂ) using 1
    funext y
    simp [momentWeightGrad, momentWeight, Complex.real_smul]
    ring

omit [FiniteDimensional ℝ E] in
/-- All first moment-phase jets have the radial L2 majorant needed for integer-image summation. -/
theorem amplitudeId_moment_jet_radial_memLp (U : PlaneHk Set.univ 1 E)
    (ϖ : ℝ) (hϖ : 0 < ϖ)
    (hm : ∀ a : JetIndex2 1, ∀ n : ℕ, (∫⁻ y, ENNReal.ofReal
      ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n * ‖U.toFunction.jet a y‖ ^ 2)) < ⊤)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (a : JetIndex2 1) :
    MemLp (fun y => (1 + ‖y‖) ^ 4 •
      multiplicationRawJet (amplitudeId_momentCoefficient θ β e) U.toFunction.jet a y) 2 volume := by
  have hvalue : U.toFunction.jet (valueIndex2 1) = planeValue U := by
    rw [planeValue_eq_stored]
    rfl
  have hscalar (a : JetIndex2 1) := amplitudeId_scalar_radial_memLp (U.toFunction.jet a)
    (by simpa only [Measure.restrict_univ] using (U.toFunction.memL2 a).aestronglyMeasurable)
    ϖ hϖ (hm a) θ β e
  rcases a with ⟨a, w⟩
  fin_cases a
  · have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    change MemLp (fun y => (1 + ‖y‖) ^ 4 •
      multiplicationRawJet (amplitudeId_momentCoefficient θ β e) U.toFunction.jet (valueIndex2 1) y) 2 volume
    simp_rw [amplitudeId_moment_jet_value]
    exact amplitudeId_scalar_radial_memLp (planeValue U)
      (planeJetOrder_memLp (Nat.zero_le _) U (fun i => i.elim0)).aestronglyMeasurable
      ϖ hϖ (fun n => by simpa only [hvalue] using hm (valueIndex2 1) n) θ β e
  · have hw : w = fun _ => w 0 := funext (fun j => congrArg w (Subsingleton.elim _ _))
    rw [hw]
    have hv := hscalar (valueIndex2 1)
    have hd := hscalar ⟨⟨1, by decide⟩, fun _ => w 0⟩
    have hg := amplitudeId_grad_radial_memLp (U.toFunction.jet (valueIndex2 1))
      (by simpa only [Measure.restrict_univ] using
        (U.toFunction.memL2 (valueIndex2 1)).aestronglyMeasurable)
      ϖ hϖ (hm (valueIndex2 1)) θ β e (w 0)
    convert (hd.add hg).sub (hv.const_mul (Complex.I * (θ (w 0) : ℂ))) using 1
    funext y
    rw [amplitudeId_moment_jet_first, planeJetOrder_eq_stored le_rfl]
    simp only [hvalue]
    simp only [Pi.add_apply, Pi.sub_apply, smul_sub,
      Complex.ofReal_add, Complex.real_smul]
    ring

omit [FiniteDimensional ℝ E] in
/-- Finite factorial energy controls the literal stored quadratic moment of every component. -/
theorem amplitudeId_stored_moment_finite {k : ℕ} (U : PlaneHk Set.univ k E)
    (n : ℕ) (ϖ r : ℝ) (hr : 0 < r)
    (he : weightedFactorialNormSq n ϖ 0 r k U ≠ ⊤) (a : JetIndex2 k) :
    (∫⁻ y, ENNReal.ofReal ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n *
      ‖U.toFunction.jet a y‖ ^ 2)) < ⊤ := by
  rw [Weighted.weightedFactorialNormSq_stored_readout] at he
  have hc := Weighted.storedChartFactorialEnergy_component_ne_top r hr _ U he a
  have heq : Weighted.chartScalarEnergy (Weighted.planeMomentPolynomial n ϖ 0)
      (Weighted.planeJetReadoutOperator k a U) =
      ∫⁻ y, ENNReal.ofReal ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n *
        ‖U.toFunction.jet a y‖ ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [Weighted.planeJetReadout_ae_raw U a] with y hy
    simp only [hy, Weighted.planeMomentPolynomial, Pi.zero_apply, sub_zero]
  exact lt_top_iff_ne_top.mpr (heq ▸ hc)

/-- Absolute integer-image summation preserves the moment-phase weak derivative identities. -/
theorem amplitudeId_periodized_moment_weakJet (U : PlaneHk Set.univ 1 E)
    (ϖ : ℝ) (hϖ : 0 < ϖ)
    (hm : ∀ a : JetIndex2 1, ∀ n : ℕ, (∫⁻ y, ENNReal.ofReal
      ((1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n * ‖U.toFunction.jet a y‖ ^ 2)) < ⊤)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) :
    HasPeriodicOrderedWeakJet (CycleJointProofs.periodizeRawJet
      (multiplicationRawJet (amplitudeId_momentCoefficient θ β e) U.toFunction.jet)) := by
  apply CycleJointProofs.periodizeRawJet_of_radial_moments _
    (amplitudeId_moment_weakJet U θ β e) 0
  · intro a
    have h := amplitudeId_moment_jet_radial_memLp U ϖ hϖ hm θ β e a
    have hc : Continuous (fun y : Vec 2 => ((1 + ‖y‖) ^ 4)⁻¹) := by
      apply Continuous.inv₀ (by fun_prop)
      intro y
      positivity
    convert hc.aestronglyMeasurable.smul h.aestronglyMeasurable using 1
    funext y
    change _ = ((1 + ‖y‖) ^ 4)⁻¹ • ((1 + ‖y‖) ^ 4 •
      multiplicationRawJet (amplitudeId_momentCoefficient θ β e) U.toFunction.jet a y)
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · intro a
    simpa only [sub_zero] using amplitudeId_moment_jet_radial_memLp U ϖ hϖ hm θ β e a

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The stage values at the start of the piece

At the start `a` the chain is its datum: level `0` is `f`, with `planeValue (f x) = φ x` a.e., and
the higher levels vanish (`frame_initial`). So a level-0 stage value is the Bloch part of
`y^β ⟨e, φ x⟩` (`frame_initial_level_zero`; `planeBlochC_congr_ae`: the Bloch part only sees the
plane function a.e.), and a higher-level stage value vanishes (`frame_initial_level_succ`). With the
level-0 identity, the squared cell norms summed over the components (weights `π_x⁻¹`)
and an orthonormal basis are the squared Bloch fibre derivative norm (`levelZero_sum_sq`); this is
dimension-free. -/

universe u v

theorem measurableSet_cellCube : MeasurableSet AVenhance.unitCube := by
  unfold AVenhance.unitCube
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- **The Bloch part only sees the plane function a.e.** -/
theorem planeBlochC_congr_ae (θ : Vec 2) {g g' : Vec 2 → ℝ} (hg : g =ᵐ[volume] g') :
    planeBlochC θ g =ᵐ[volume.restrict AVenhance.unitCube] planeBlochC θ g' := by
  have hk : ∀ k : Fin 2 → ℤ, (fun z : Vec 2 => g (z + fun i => (k i : ℝ))) =ᵐ[volume]
      fun z => g' (z + fun i => (k i : ℝ)) := fun k =>
    (measurePreserving_add_right volume (fun i => (k i : ℝ))).quasiMeasurePreserving.ae_eq_comp hg
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_all_iff.2 hk] with z hz
  unfold planeBlochC
  exact tsum_congr fun k => by rw [hz k]

/-- The Bloch part of a measurable function is measurable. -/
theorem measurable_planeBlochC (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Measurable g) :
    Measurable (planeBlochC θ g) := by
  unfold planeBlochC
  refine Measurable.tsum fun k => ?_
  have hdot : Continuous fun z : Vec 2 => vecDot θ (z + fun i => (k i : ℝ)) := by
    unfold vecDot
    fun_prop
  have hgk : Measurable fun z : Vec 2 => g (z + fun i => (k i : ℝ)) :=
    hg.comp (measurable_id.add_const _)
  exact (Complex.continuous_exp.comp ((continuous_const.mul
    (Complex.continuous_ofReal.comp hdot)).neg)).measurable.mul (Complex.measurable_ofReal.comp hgk)

/-- The squared norm of a cell `L²` class is the cell integral of its squared modulus. -/
theorem cellL2_ofReal_norm_sq (u : ComplexCellL2) :
    ENNReal.ofReal (‖u‖ ^ 2) = ∫⁻ z in AVenhance.unitCube, ‖u z‖ₑ ^ 2 := by
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (Lp.aestronglyMeasurable u)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- **The chain at the start of the piece** is its datum. -/
theorem frame_initial {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (j : Fin (Nw + 1))
    (x : ι) : F.u j x F.a = chainDatum F.κ F.f j x :=
  F.solution.2.2.2.1 (j, x)

/-- A level-0 stage value at the start is the Bloch part of the datum. -/
theorem frame_initial_level_zero {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (x : ι)
    (e : h x) (β : ℕ × ℕ) :
    planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u 0 x F.a) y)) =ᵐ[
      volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight β y * inner ℝ e (F.φ x y)) := by
  refine planeBlochC_congr_ae θ ?_
  rw [frame_initial, chainDatum_zero]
  filter_upwards [F.datum x] with y hy
  rw [hy]

/-- A higher-level stage value at the start vanishes. -/
theorem frame_initial_level_succ {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (j : Fin (Nw + 1)) (hj : j ≠ 0) (x : ι) (e : h x) (β : ℕ × ℕ) :
    planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x F.a) y)) =ᵐ[
      volume.restrict AVenhance.unitCube] 0 := by
  have hz : F.u j x F.a = 0 := by
    rw [frame_initial]
    simp [chainDatum, hj]
  have h0 : planeBlochC θ (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
    funext z
    simp [planeBlochC]
  rw [← h0]
  refine planeBlochC_congr_ae θ ?_
  rw [hz]
  filter_upwards [planeValue_zero_ae (E := h x) (F.κ j x)] with y hy
  rw [hy, inner_zero_right, mul_zero]

end Frame

/-- **The level-0 identity summed over the components**: for strongly measurable
compactly supported data and orthonormal bases, `∑_x π_x⁻¹ ∑_e ∫_cell |B_θ(y^β⟨b_e, φ_x⟩)|²` is
the squared Bloch fibre derivative norm. -/
theorem levelZero_sum_sq (hL : LevelZeroDataStatement.{v}) {ι : Type u} [Fintype ι]
    {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] (π : ι → ℝ) (φ : ∀ x, Vec 2 → h x)
    (hφ : ∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x)) (β : ℕ × ℕ) (θ : Vec 2) :
    ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
        ∫⁻ z in AVenhance.unitCube, ‖planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e) (φ x y)) z‖ₑ ^ 2 =
      blochFibreDerivNorm π (fun _ => 1) β φ θ ^ 2 := by
  have hmeas : ∀ x (e : Fin (Module.finrank ℝ (h x))), Measurable fun z =>
      ‖planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) e) (φ x y)) z‖ₑ ^ 2 := by
    intro x e
    have hc : Measurable fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) e) (φ x y) := by
      unfold momentWeight
      exact (by fun_prop : Measurable fun y : Vec 2 => y 0 ^ β.1 * y 1 ^ β.2).mul
        ((continuous_const.inner continuous_id).comp_stronglyMeasurable (hφ x).1).measurable
    exact ((measurable_planeBlochC θ hc).enorm).pow_const 2
  unfold blochFibreDerivNorm
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  symm
  -- the pointwise identity on the cell
  have hpt : Set.EqOn (fun z => ∑ x, ENNReal.ofReal (π x)⁻¹ *
      (‖thetaPartial β.1 β.2 (fun θ' => blochCos θ' (φ x) z) θ‖ₑ ^ 2 +
        ‖thetaPartial β.1 β.2 (fun θ' => blochSin θ' (φ x) z) θ‖ₑ ^ 2))
      (fun z => ∑ x, ENNReal.ofReal (π x)⁻¹ * ∑ e : Fin (Module.finrank ℝ (h x)),
        ‖planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e) (φ x y)) z‖ₑ ^ 2) AVenhance.unitCube := by
    intro z hz
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    have hl := hL (stdOrthonormalBasis ℝ (h x)) (φ x) (hφ x).2 β θ z hz
    set dc := thetaPartial β.1 β.2 (fun θ' => blochCos θ' (φ x) z) θ with hdc
    set ds := thetaPartial β.1 β.2 (fun θ' => blochSin θ' (φ x) z) θ with hds
    have e1 : ‖dc‖ₑ ^ 2 + ‖ds‖ₑ ^ 2 = ENNReal.ofReal (‖dc‖ ^ 2 + ‖ds‖ ^ 2) := by
      rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm]
    rw [e1, ← hl, ENNReal.ofReal_sum_of_nonneg fun e _ => sq_nonneg _]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [setLIntegral_congr_fun measurableSet_cellCube hpt]
  rw [lintegral_finsetSum _ fun x _ =>
    (Finset.measurable_sum _ fun e _ => hmeas x e).const_mul _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun e _ => hmeas x e),
    lintegral_finsetSum _ fun e _ => hmeas x e]

end AVRegularity.CycleWords.Assembly
end

section
namespace AVRegularity.CycleWords.Assembly

/-! # The regularity ladder of the stages

The test norm of stage `k` is `H^{s_k}` with
`s(j, β) = s₀ + ∑_{l<j} (d_l + K_s(l)) + |β|` (`b1wLadder`). A stage is determined by its
index `k` (`level = k mod (N_w+1)`, `degree = k div (N_w+1)`; `b1wSt_level`, `b1wSt_deg`), so the
ladder is a function of `k` (`b1wLadderAt`, `b1wLadderAt_eq`).

* **Same level**, lower moment: the ladder drops by `|β| - |β'| ≥ 1` (`b1wLadder_same_le`).
* **Letter** from level `l` to `l + 1` with `|β''| ≤ |β| + K_s(l)`: the ladder drops by at least
  `d_l` (`b1wLadder_letter_le`).
* **Top**: `s ≤ s₀ + ∑ d + ∑ K_s + n₀` with `n₀ = m + ∑ K_s` (`b1wLadder_le`).

This is the derivative budget of a word: each letter spends `d_l`, each moment step spends `1`. -/

universe u v

/-- The ladder offset of level `j`: `∑_{l<j} (d_l + K_s(l))`. -/
def b1wLadderLevel {Nw : ℕ} (d Ks : Fin Nw → ℕ) (j : Fin (Nw + 1)) : ℕ :=
  ∑ l : Fin Nw, if l.val < j.val then d l + Ks l else 0

theorem b1wLadderLevel_succ {Nw : ℕ} (d Ks : Fin Nw → ℕ) (l : Fin Nw) :
    b1wLadderLevel d Ks l.succ = b1wLadderLevel d Ks l.castSucc + (d l + Ks l) := by
  unfold b1wLadderLevel
  have hsplit : (∑ l' : Fin Nw, if l'.val < l.succ.val then d l' + Ks l' else 0) =
      ∑ l' : Fin Nw, ((if l'.val < l.castSucc.val then d l' + Ks l' else 0) +
        (if l' = l then d l' + Ks l' else 0)) := by
    refine Finset.sum_congr rfl fun l' _ => ?_
    simp only [Fin.val_succ, Fin.val_castSucc]
    by_cases h1 : l' = l
    · subst h1
      simp
    · have hne : l'.val ≠ l.val := fun e => h1 (Fin.ext e)
      simp only [h1, ite_false, add_zero]
      split_ifs <;> omega
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ l]
  simp

section Index

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The regularity ladder of a stage. -/
def b1wLadder (s₀ : ℕ) (d : Fin Nw → ℕ) (i : B1WIndex ι h Nw m Ks) : ℕ :=
  s₀ + b1wLadderLevel d Ks i.1 + (i.2.2.1.1.1 + i.2.2.1.1.2)

/-- The level of a stage index. -/
theorem b1wSt_level (i : B1WIndex ι h Nw m Ks) : i.1.val = b1wSt i % (Nw + 1) := by
  unfold b1wSt
  rw [Nat.mul_add_mod_of_lt i.1.isLt]

/-- The degree of a stage index. -/
theorem b1wSt_deg (i : B1WIndex ι h Nw m Ks) : b1wDeg i = b1wSt i / (Nw + 1) := by
  unfold b1wSt
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos Nw), Nat.div_eq_of_lt i.1.isLt,
    zero_add]

/-- The ladder as a function of the stage index. -/
def b1wLadderAt (Nw : ℕ) (s₀ : ℕ) (d Ks : Fin Nw → ℕ) (k : ℕ) : ℕ :=
  s₀ + b1wLadderLevel d Ks ⟨k % (Nw + 1), Nat.mod_lt _ (Nat.succ_pos Nw)⟩ +
    (k / (Nw + 1) - b1wPrefix Ks ⟨k % (Nw + 1), Nat.mod_lt _ (Nat.succ_pos Nw)⟩)

theorem b1wLadderAt_eq (s₀ : ℕ) (d : Fin Nw → ℕ) (i : B1WIndex ι h Nw m Ks) :
    b1wLadderAt Nw s₀ d Ks (b1wSt i) = b1wLadder s₀ d i := by
  have hl : (⟨b1wSt i % (Nw + 1), Nat.mod_lt _ (Nat.succ_pos Nw)⟩ : Fin (Nw + 1)) = i.1 :=
    Fin.ext (b1wSt_level i).symm
  unfold b1wLadderAt b1wLadder
  rw [hl, ← b1wSt_deg]
  unfold b1wDeg
  congr 1
  omega

/-- **Same level**: a lower moment has a ladder lower by the moment drop. -/
theorem b1wLadder_same_le (s₀ : ℕ) (d : Fin Nw → ℕ) (i i' : B1WIndex ι h Nw m Ks)
    (hj : i'.1 = i.1) (hβ : i'.2.2.1.1.1 + i'.2.2.1.1.2 + 1 ≤ i.2.2.1.1.1 + i.2.2.1.1.2) :
    b1wLadder s₀ d i' + 1 ≤ b1wLadder s₀ d i := by
  have h1 : b1wLadderLevel d Ks i'.1 = b1wLadderLevel d Ks i.1 := by rw [hj]
  unfold b1wLadder
  omega

/-- **Letter**: from level `l` to `l + 1`, the ladder drops by at least `d_l`. -/
theorem b1wLadder_letter_le (s₀ : ℕ) (d : Fin Nw → ℕ) (l : Fin Nw) (i i' : B1WIndex ι h Nw m Ks)
    (hj : i.1 = l.succ) (hj' : i'.1 = l.castSucc)
    (hβ : i'.2.2.1.1.1 + i'.2.2.1.1.2 ≤ i.2.2.1.1.1 + i.2.2.1.1.2 + Ks l) :
    b1wLadder s₀ d i' + d l ≤ b1wLadder s₀ d i := by
  have h1 : b1wLadderLevel d Ks i.1 = b1wLadderLevel d Ks l.castSucc + (d l + Ks l) := by
    rw [hj, b1wLadderLevel_succ]
  have h2 : b1wLadderLevel d Ks i'.1 = b1wLadderLevel d Ks l.castSucc := by rw [hj']
  unfold b1wLadder
  omega

/-- **Top of the ladder.** -/
theorem b1wLadder_le (s₀ : ℕ) (d : Fin Nw → ℕ) (i : B1WIndex ι h Nw m Ks) :
    b1wLadder s₀ d i ≤ s₀ + (∑ l, d l + ∑ l, Ks l) + (m + ∑ l, Ks l) := by
  have hβ := (Finset.mem_filter.1 i.2.2.1.2).2
  have hlev : b1wLevelMoments m Ks i.1 ≤ m + ∑ l, Ks l := by
    have := b1wPrefix_add_levelMoments m Ks i.1
    omega
  have hL : b1wLadderLevel d Ks i.1 ≤ ∑ l, d l + ∑ l, Ks l := by
    unfold b1wLadderLevel
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun l _ => by split_ifs <;> omega
  unfold b1wLadder
  omega

end Index

theorem b1wPrefix_succ {Nw : ℕ} (Ks : Fin Nw → ℕ) (l : Fin Nw) :
    b1wPrefix Ks l.succ = b1wPrefix Ks l.castSucc + Ks l := by
  unfold b1wPrefix
  have hsplit : (∑ l' : Fin Nw, if l'.val < l.succ.val then Ks l' else 0) =
      ∑ l' : Fin Nw, ((if l'.val < l.castSucc.val then Ks l' else 0) +
        (if l' = l then Ks l' else 0)) := by
    refine Finset.sum_congr rfl fun l' _ => ?_
    simp only [Fin.val_succ, Fin.val_castSucc]
    by_cases h1 : l' = l
    · subst h1
      simp
    · have hne : l'.val ≠ l.val := fun e => h1 (Fin.ext e)
      simp only [h1, ite_false, add_zero]
      split_ifs <;> omega
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ l]
  simp

section Pairs

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **An earlier stage at the same level has a lower ladder by at least one.** -/
theorem b1wLadder_same_of_lt (s₀ : ℕ) (d : Fin Nw → ℕ) (i i' : B1WIndex ι h Nw m Ks)
    (hj : i'.1 = i.1) (hlt : b1wSt i' < b1wSt i) :
    b1wLadder s₀ d i' + 1 ≤ b1wLadder s₀ d i := by
  refine b1wLadder_same_le s₀ d i i' hj ?_
  have hp : b1wPrefix Ks i'.1 = b1wPrefix Ks i.1 := by rw [hj]
  have hv : i'.1.val = i.1.val := by rw [hj]
  unfold b1wSt b1wDeg at hlt
  rw [hp, hv] at hlt
  have := Nat.lt_of_add_lt_add_right hlt
  have h2 := (Nat.mul_lt_mul_right (Nat.succ_pos Nw)).1 this
  omega

/-- **An earlier stage at the previous level has a lower ladder by at least `d_l`.** -/
theorem b1wLadder_letter_of_lt (s₀ : ℕ) (d : Fin Nw → ℕ) (l : Fin Nw)
    (i i' : B1WIndex ι h Nw m Ks) (hj : i.1 = l.succ) (hj' : i'.1 = l.castSucc)
    (hlt : b1wSt i' < b1wSt i) : b1wLadder s₀ d i' + d l ≤ b1wLadder s₀ d i := by
  refine b1wLadder_letter_le s₀ d l i i' hj hj' ?_
  have hp : b1wPrefix Ks i.1 = b1wPrefix Ks l.castSucc + Ks l := by rw [hj, b1wPrefix_succ]
  have hp' : b1wPrefix Ks i'.1 = b1wPrefix Ks l.castSucc := by rw [hj']
  have hv : i.1.val = l.val + 1 := by rw [hj, Fin.val_succ]
  have hv' : i'.1.val = l.val := by rw [hj', Fin.val_castSucc]
  unfold b1wSt b1wDeg at hlt
  rw [hp, hp', hv, hv'] at hlt
  have hdeg : i'.2.2.1.1.1 + i'.2.2.1.1.2 + b1wPrefix Ks l.castSucc ≤
      i.2.2.1.1.1 + i.2.2.1.1.2 + (b1wPrefix Ks l.castSucc + Ks l) := by
    by_contra hc
    push Not at hc
    have h1 : (i.2.2.1.1.1 + i.2.2.1.1.2 + (b1wPrefix Ks l.castSucc + Ks l) + 1) * (Nw + 1) ≤
        (i'.2.2.1.1.1 + i'.2.2.1.1.2 + b1wPrefix Ks l.castSucc) * (Nw + 1) :=
      Nat.mul_le_mul_right _ hc
    have h2 : (i.2.2.1.1.1 + i.2.2.1.1.2 + (b1wPrefix Ks l.castSucc + Ks l) + 1) * (Nw + 1) =
        (i.2.2.1.1.1 + i.2.2.1.1.2 + (b1wPrefix Ks l.castSucc + Ks l)) * (Nw + 1) + (Nw + 1) := by
      ring
    have hl := l.isLt
    omega
  omega

end Pairs

end AVRegularity.CycleWords.Assembly
end
