-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.Part1
public import AVRegularity.Construction.Residual.Presentation.Cascade.InnerOrderFacts
public import AVRegularity.Construction.Residual.Presentation.Cascade.FilterInputs
import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedCertificates
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Residual.Presentation.Cascade.CtxFineTail
import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelope

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.CovOp AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.CycleComparison.LiftMeanEntrywise
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Assembly
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Realized diagonal and inherited mean flux bounds for the covariance G form.
The common native slot-lift input acts on the covariance-filtered readout gradient. Its
price contains the parent diffusivity, cancelling the gradient energy's inverse
price. Radius reduction keeps the same realization. The cases `p = 0`, empty
components, zero datum, empty positive grades and point windows need no changes. -/

section Radius
variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

private theorem flux_radius {K : ℕ} {I : Set ℝ} {ν r R : ℝ} {π : ι → ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (hrR : r ≤ R) (hπ : ∀ v, 0 < π v)
    {F : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} {Y : ℝ}
    (hf : HasFluxBound K I ν R π F Y) : HasFluxBound K I ν r π F Y := by
  obtain ⟨U, hu, hm⟩ := hf
  refine ⟨U, hu, hm.1, le_trans (Real.sqrt_le_sqrt ?_) hm.2⟩
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hν.le)
  apply integral_mono_ae (covOp_mass_integrable r π hπ I U hm.1)
    (covOp_mass_integrable R π hπ I U hm.1)
  exact Filter.Eventually.of_forall fun t => Finset.sum_le_sum fun v _ =>
    mul_le_mul_of_nonneg_left
      (CycleJointProofs.factorialNormSq_mono_radius hr hrR (U v t).val)
      (inv_nonneg.mpr (hπ v).le)
end Radius

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
  (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The exact input order of the physical finite-degree coefficient action. -/
def CovGInputOrder (kc : ℕ) : ℕ := kc + 6 * F.p + F.N + Dm

/-- Source grades before reference subtraction. -/
def CovGRawGrades (depth : ℕ) (diagonal : Bool) : Finset ℕ :=
  if diagonal then {0} else Finset.Icc 1 depth

/-- The common native coefficient price without physical diffusivity. -/
def CovGRawPrice (diagonal : Bool) (kc Acl ell : ℕ)
    (CG CW : ℕ → ℝ) (Ca Sb : ℝ) : ℝ :=
  covTruncGradientCoefficientConst (kc + 4 * F.p) (F.N + Dm) *
    CovGNativeCEConst F.N Dm (kc + 4 * F.p)
      (CovGLetterConst F Acl ell CG CW Ca) *
        ∑ hh ∈ CovGRawGrades F.depth diagonal, Sb ^ hh

private theorem input_regular (kc : ℕ)
    (ho : CovGInputOrder F kc + 1 ≤ F.Naux) :
    ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((kc + 4 * F.p + (F.N + Dm) + 1 : ℕ) : ℕ∞)
        (fun y => menuCovPRep F.Mn D F.m F.p F.aZ t y v) ∧
      IsZ2Periodic (fun y => menuCovPRep F.Mn D F.m F.p F.aZ t y v) := by
  intro v t ht
  have hf : ContDiff ℝ ((F.Naux : ℕ) : ℕ∞) (fun y => F.aZ t y v) := by
    exact_mod_cast (F.readout v t ht).2.1
  have hneed : kc + 4 * F.p + (F.N + Dm) + 1 + 2 * F.p ≤ F.Naux := by
    unfold CovGInputOrder at ho; omega
  refine ⟨covOp_contDiff_P _ F.p _ (hf.of_le (by exact_mod_cast hneed)), ?_⟩
  exact covOp_periodic_P _ F.p (hf.of_le (by exact_mod_cast (by omega : 2 * F.p ≤ F.Naux)))
    (F.readout v t ht).2.2.1

/-- The covariance polynomial maps the higher readout gradient to the exact filtered one. -/
theorem CovGFilteredGradient (kc : ℕ) (g : CovGNativeWindow F law)
    (ho : CovGInputOrder F kc + 1 ≤ F.Naux)
    (hs : CovSizeForm F.Mn D F.m F.tp F.tf (fRho F) 1) {E : ℝ}
    (hg : HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root)
      (CovGInputOrder F kc) (Set.Icc F.tp F.tf) (D.κ (F.m - 1))
      (fRho F) (F.G.mass law) (fun v t y => toFluxL (gradE (fun z => F.aZ t z v) y)) E) :
    HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root)
      (kc + 4 * F.p + (F.N + Dm)) (Set.Icc F.tp F.tf) (D.κ (F.m - 1))
      (fRho F) (F.G.mass law)
      (fun v t y => toFluxL (gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y))
      (covPolyConst (4 * ((CovGInputOrder F kc : ℕ) : ℝ) ^ 2) F.p * E) := by
  have hf : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((2 * F.p + 1 : ℕ) : ℕ∞) (fun z => F.aZ t z v) := by
    intro v t ht
    have h : 2 * F.p + 1 ≤ F.Naux := by unfold CovGInputOrder at ho; omega
    exact (F.readout v t ht).2.1.of_le (by exact_mod_cast h)
  have hgrad : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((2 * F.p : ℕ) : ℕ∞)
        (fun y => toFluxL (gradE (fun z => F.aZ t z v) y)) := by
    intro v t ht
    exact_mod_cast contDiff_gradField_nat (hf v t ht)
  let T := covTruncCovGradient_operator (h := fun v : CompIn F.G.comps => hr v.1.root)
    (kc + 4 * F.p + (F.N + Dm)) F.p F.tp F.tf (fRho F) g.rho_pos
    (F.G.mass law) g.mass_pos (fun t => menuCovPrimitive D F.Mn F.m t)
    hs.2.2.2 (fun t ht => (hs.1 t ht).trans (by
      simp only [one_mul]
      exact le_mul_of_one_le_left (sq_nonneg _) (by norm_num)))
    (fun v t y => toFluxL (gradE (fun z => F.aZ t z v) y)) hgrad
    (fun v t ht z y => by
      apply PiLp.ext
      intro j
      exact covTruncReg_gradE_periodic ((hf v t ht).differentiable (by simp))
        (F.readout v t ht).2.2.1 j z y)
    (fun v t ht => (covOp_contDiff_P _ F.p 0
      (by simpa only [zero_add] using hgrad v t ht)).continuous)
  have he : kc + 4 * F.p + (F.N + Dm) + 2 * F.p = CovGInputOrder F kc := by
    unfold CovGInputOrder; omega
  have hC : 0 ≤ covPolyConst (4 * ((CovGInputOrder F kc : ℕ) : ℝ) ^ 2) F.p := by
    unfold covPolyConst
    exact Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg (by positivity) l) (Nat.cast_nonneg _)
  have hg' := hg
  rw [← he] at hg'
  have hb := T.hasFluxBound measurableSet_Icc g.B_pos g.mass_pos (he ▸ hC) hg'
  rw [he] at hb
  obtain ⟨U, hu, hm⟩ := hb
  refine ⟨U, ?_, hm⟩
  intro v t ht
  have htarg : (fun y => toFluxL (gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y)) =
      covPolyP (menuCovPrimitive D F.Mn F.m t) F.p
        (fun y => toFluxL (gradE (fun z => F.aZ t z v) y)) := by
    funext y
    exact covTruncGradient_covPolyP_finite _ F.p (fun z => F.aZ t z v) (hf v t ht) y
  change (U v t).toFunction.jet _ =ᵐ[volume.restrict unitCube] _
  exact (hu v t ht).trans (Filter.Eventually.of_forall fun y => (congrFun htarg y).symm)

/-- The actual coefficient data for either raw grade range, at a uniform enlarged price. -/
theorem CovGRaw_data {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (kc : ℕ) (diagonal : Bool)
    (hN : 1 ≤ F.N) (hDm : 1 ≤ Dm) (hfamily : CovGFamily F) (hSb : 0 ≤ Sb)
    (hK : kc + 4 * F.p ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (ho : CovGInputOrder F kc + 1 ≤ F.Naux) {C : ℝ}
    (hC : CovGRawPrice F diagonal kc Acl ell CG CW Ca Sb ≤ C) :
    Nonempty (CovTruncCoefficientData (h := fun v : CompIn F.G.comps => hr v.1.root)
      (kc + 4 * F.p) (F.N + Dm) F.tp F.tf (fRho F) (C * D.κ (F.m - 1))
      (F.G.mass law)
      (fun v t y => toFluxL (gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y))
      (fun v t y => toFluxL (menuGluedMeanFlux F.Mn F.G F.m (CovGRawGrades F.depth diagonal)
        (if diagonal then Finset.Icc 2 (F.N + 1) else Finset.Icc 2 (F.N + Dm)) F.CcT
        (menuCovPRep F.Mn D F.m F.p F.aZ) t y v))) := by
  have hend : F.tp + fTobs F = F.tf := by unfold fTobs; ring
  have hf := input_regular F kc ho
  obtain ⟨P⟩ := CovGNativeGrade_data F law p hA (kc + 4 * F.p) hK g hN hfamily hSb
    (CovGRawGrades F.depth diagonal) (fun hh hhh => by
      cases diagonal <;> simp only [CovGRawGrades, ↓reduceIte] at hhh
      · exact (Finset.mem_Icc.mp hhh).2
      · have hz := Finset.mem_singleton.mp hhh
        subst hh; exact Nat.zero_le _) (menuCovPRep F.Mn D F.m F.p F.aZ)
    (fun v t ht => (hf v t (hend ▸ ht)).1) (fun v t ht => (hf v t (hend ▸ ht)).2)
  have hc : covTruncGradientCoefficientConst (kc + 4 * F.p) (F.N + Dm) *
      (D.κ (F.m - 1) * CovGNativeCEConst F.N Dm (kc + 4 * F.p)
        (CovGLetterConst F Acl ell CG CW Ca) *
          ∑ hh ∈ CovGRawGrades F.depth diagonal, Sb ^ hh) =
      CovGRawPrice F diagonal kc Acl ell CG CW Ca Sb * D.κ (F.m - 1) := by
    unfold CovGRawPrice; ring
  rw [hc, hend] at P
  have hCb := mul_le_mul_of_nonneg_right hC g.B_pos.le
  refine ⟨{ P with
    row := fun v => (P.row v).trans hCb
    col := fun u => (P.col u).trans hCb
    action := fun v t ht y => ?_ }⟩
  cases diagonal
  · exact P.action v t ht y
  · change toFluxL (menuGluedMeanFlux _ _ _ {0} (Finset.Icc 2 (F.N + 1)) _ _ t y v) = _
    rw [← CovGNativeDiag_tail F law p hA g hN hDm _ t
      (contDiff_pi.mpr fun u => ((hf u t ht).1).of_le (by exact_mod_cast (by omega :
        F.N + Dm ≤ kc + 4 * F.p + (F.N + Dm) + 1))) (hend.symm ▸ ht) y v]
    exact P.action v t ht y

/-- Apply the native coefficient operator to the already filtered gradient. -/
theorem CovGRaw_bound {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (kc : ℕ) (diagonal : Bool)
    (hN : 1 ≤ F.N) (hDm : 1 ≤ Dm) (hfamily : CovGFamily F) (hSb : 0 ≤ Sb)
    (hK : kc + 4 * F.p ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (ho : CovGInputOrder F kc + 1 ≤ F.Naux) {C E : ℝ} (hC0 : 0 ≤ C)
    (hC : CovGRawPrice F diagonal kc Acl ell CG CW Ca Sb ≤ C)
    (hg : HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root)
      (kc + 4 * F.p + (F.N + Dm)) (Set.Icc F.tp F.tf) (D.κ (F.m - 1))
      (fRho F) (F.G.mass law)
      (fun v t y => toFluxL (gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y))
      (E / D.κ (F.m - 1))) :
    HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root) (kc + 4 * F.p)
      (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (fRho F) (F.G.mass law)
      (fun v t y => toFluxL (menuGluedMeanFlux F.Mn F.G F.m (CovGRawGrades F.depth diagonal)
        (if diagonal then Finset.Icc 2 (F.N + 1) else Finset.Icc 2 (F.N + Dm)) F.CcT
        (menuCovPRep F.Mn D F.m F.p F.aZ) t y v)) (C * E) := by
  obtain ⟨P⟩ := CovGRaw_data F law p hA g kc diagonal hN hDm hfamily hSb hK ho hC
  have hb := (P.toFluxOperator g.rho_pos g.mass_pos).hasFluxBound measurableSet_Icc
    g.B_pos g.mass_pos (mul_nonneg hC0 g.B_pos.le) hg
  have he : (C * D.κ (F.m - 1)) * (E / D.κ (F.m - 1)) = C * E := by
    field_simp [g.B_pos.ne']
  rw [he] at hb
  exact hb

/-- The reference matrix costs only the ledger constant plus the two identity entries. -/
theorem CovGReferenceMatrix (Cn : ℝ) (hCn : 0 ≤ Cn) (hB : 0 < D.κ (F.m - 1))
    (hc : Continuous (covGradN D F.m))
    (hb : ∀ t, ∑ jl : Fin 2 × Fin 2, |covGradN D F.m t jl.1 jl.2| ≤ Cn * D.κ (F.m - 1)) :
    Continuous (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) ∧ 0 ≤ Cn + 2 ∧
      ∀ t, ∑ jl : Fin 2 × Fin 2,
        |ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t jl.1 jl.2| ≤ (Cn + 2) * D.κ (F.m - 1) := by
  have he : ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) =
      fun t => covGradN D F.m t + D.κ (F.m - 1) • 1 := by
    funext t
    unfold covGradN
    abel
  refine ⟨by rw [he]; exact hc.add continuous_const, add_nonneg hCn (by norm_num), fun t => ?_⟩
  rw [he]
  have hId : ∑ jl : Fin 2 × Fin 2,
      |(D.κ (F.m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) jl.1 jl.2| = 2 * D.κ (F.m - 1) := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      abs_of_pos hB, two_mul]
  calc
    _ ≤ ∑ jl : Fin 2 × Fin 2,
        (|covGradN D F.m t jl.1 jl.2| + |(D.κ (F.m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) jl.1 jl.2|) :=
      Finset.sum_le_sum fun jl _ => abs_add_le _ _
    _ = (∑ jl : Fin 2 × Fin 2, |covGradN D F.m t jl.1 jl.2|) + 2 * D.κ (F.m - 1) := by
      rw [Finset.sum_add_distrib, hId]
    _ ≤ Cn * D.κ (F.m - 1) + 2 * D.κ (F.m - 1) := add_le_add (hb t) le_rfl
    _ = _ := by ring

/-- The reference matrix acts on the same filtered gradient carrier, with no time price. -/
theorem CovGReference_bound (kc : ℕ) (g : CovGNativeWindow F law)
    (ho : CovGInputOrder F kc + 1 ≤ F.Naux) {C E : ℝ} (hC : 0 ≤ C)
    (hc : Continuous (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)))
    (hb : ∀ t, ∑ jl : Fin 2 × Fin 2,
      |ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t jl.1 jl.2| ≤ C * D.κ (F.m - 1))
    (hg : HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root)
      (kc + 4 * F.p + (F.N + Dm)) (Set.Icc F.tp F.tf) (D.κ (F.m - 1))
      (fRho F) (F.G.mass law)
      (fun v t y => toFluxL (gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y))
      (E / D.κ (F.m - 1))) :
    HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root) (kc + 4 * F.p)
      (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (fRho F) (F.G.mass law)
      (fun v t y => toFluxL (fun j => ∑ l : Fin 2,
        ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j l •
          gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y l)) (C * E) := by
  let u := fun v t y => menuCovPRep F.Mn D F.m F.p F.aZ t y v
  have hf := input_regular F kc ho
  have hreg : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((kc + 4 * F.p + 2 * 0 + 1 : ℕ) : WithTop ℕ∞) (u v t) ∧
      IsZ2Periodic (u v t) := by
    intro v t ht
    have hf' : ContDiff ℝ ((kc + 4 * F.p + (F.N + Dm) + 1 : ℕ) : ℕ∞) (u v t) := by
      exact_mod_cast (hf v t ht).1
    have hsmall : ContDiff ℝ ((kc + 4 * F.p + 1 : ℕ) : ℕ∞) (u v t) :=
      hf'.of_le (by exact_mod_cast (by omega :
        kc + 4 * F.p + 1 ≤ kc + 4 * F.p + (F.N + Dm) + 1))
    exact ⟨by exact_mod_cast hsmall, (hf v t ht).2⟩
  have hl := covTruncFluxBound_lower (by omega : kc + 4 * F.p ≤ kc + 4 * F.p + (F.N + Dm))
    measurableSet_Icc g.B_pos g.mass_pos hg
  have hflux := EntryTerminal.CovGrad.covGrad_flux
    (h := fun v : CompIn F.G.comps => hr v.1.root) (kc + 4 * F.p) 0
    measurableSet_Icc (D.κ (F.m - 1)) (fRho F) (F.G.mass law) g.B_pos g.rho_pos g.mass_pos
    (fun _ => 0) (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) 0 (C * D.κ (F.m - 1))
    continuousOn_const hc.continuousOn le_rfl (fun t _ => by simp [covBound])
    (fun t _ => hb t) (mul_nonneg hC g.B_pos.le) u (E / D.κ (F.m - 1)) hreg hl
  simp only [Nat.mul_zero, Nat.add_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_mul, Function.iterate_zero, id_eq, one_smul] at hflux
  have he : (C * D.κ (F.m - 1)) * (E / D.κ (F.m - 1)) = C * E := by
    field_simp [g.B_pos.ne']
  rw [he] at hflux
  exact hflux

/-- The inherited mean flux has exactly the bound of its positive grade operator. -/
theorem CovGMean_bound {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (kc : ℕ) (hN : 1 ≤ F.N) (hDm : 1 ≤ Dm)
    (hfamily : CovGFamily F) (hSb : 0 ≤ Sb)
    (hK : kc + 4 * F.p ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (ho : CovGInputOrder F kc + 1 ≤ F.Naux) {C E cr : ℝ} (hC0 : 0 ≤ C)
    (hC : CovGRawPrice F false kc Acl ell CG CW Ca Sb ≤ C)
    (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hg : HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root)
      (kc + 4 * F.p + (F.N + Dm)) (Set.Icc F.tp F.tf) (D.κ (F.m - 1))
      (fRho F) (F.G.mass law)
      (fun v t y => toFluxL (gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y))
      (E / D.κ (F.m - 1))) : CovGTermAt 2 F law cr kc (C * E) := by
  have hr := CovGRaw_bound F law p hA g kc false hN hDm hfamily hSb hK ho hC0 hC hg
  have hsmall : rhoEnh D cr F.m ≤ fRho F := by
    change cr * liftLength D F.m ≤ liftLength D F.m
    simpa only [fRho, liftLength, one_mul] using mul_le_mul_of_nonneg_right hcr1 g.rho_pos.le
  have hr0 : 0 ≤ rhoEnh D cr F.m := mul_nonneg hcr.le g.rho_pos.le
  simpa only [CovGTermAt, CovGTerm, CovGRawGrades, Bool.false_eq_true,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ↓reduceIte, gMeanTerm, menuMeanFluxE] using flux_radius g.B_pos hr0 hsmall g.mass_pos hr

/-- Grade zero minus the reference matrix is the literal diagonal target. -/
theorem CovGDiag_bound {Acl ell : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (kc : ℕ) (hN : 1 ≤ F.N) (hDm : 1 ≤ Dm)
    (hfamily : CovGFamily F) (hSb : 0 ≤ Sb)
    (hK : kc + 4 * F.p ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (ho : CovGInputOrder F kc + 1 ≤ F.Naux) {C Cref E cr : ℝ} (hC0 : 0 ≤ C)
    (hC : CovGRawPrice F true kc Acl ell CG CW Ca Sb ≤ C)
    (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hJ : Continuous (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) ∧ 0 ≤ Cref ∧
      ∀ t, ∑ jl : Fin 2 × Fin 2,
        |ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t jl.1 jl.2| ≤ Cref * D.κ (F.m - 1))
    (hg : HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root)
      (kc + 4 * F.p + (F.N + Dm)) (Set.Icc F.tp F.tf) (D.κ (F.m - 1))
      (fRho F) (F.G.mass law)
      (fun v t y => toFluxL (gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y))
      (E / D.κ (F.m - 1))) : CovGTermAt 1 F law cr kc ((C + Cref) * E) := by
  have hraw := CovGRaw_bound F law p hA g kc true hN hDm hfamily hSb hK ho hC0 hC hg
  have href := CovGReference_bound F law kc g ho hJ.2.1 hJ.1 hJ.2.2 hg
  have hd := covTruncSub _ _ _ _ _ g.B_pos g.mass_pos _ _ _ _ hraw href
  have hsmall : rhoEnh D cr F.m ≤ fRho F := by
    change cr * liftLength D F.m ≤ liftLength D F.m
    simpa only [fRho, liftLength, one_mul] using mul_le_mul_of_nonneg_right hcr1 g.rho_pos.le
  have hr0 : 0 ≤ rhoEnh D cr F.m := mul_nonneg hcr.le g.rho_pos.le
  have hd' := flux_radius g.B_pos hr0 hsmall g.mass_pos hd
  have he : C * E + Cref * E = (C + Cref) * E := by ring
  rw [he] at hd'
  change HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root) (kc + 4 * F.p)
    (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law)
    (fun v t y => toFluxL (menuGluedMeanFlux F.Mn F.G F.m {0} (Finset.Icc 2 (F.N + 1))
      F.CcT (menuCovPRep F.Mn D F.m F.p F.aZ) t y v -
      fun j => ∑ l : Fin 2, ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j l •
        gradE (fun z => menuCovPRep F.Mn D F.m F.p F.aZ t z v) y l)) ((C + Cref) * E)
  simpa only [CovGRawGrades, ↓reduceIte, toFluxL, WithLp.toLp_sub] using hd' 

/-- Full-lift energy supplies the higher readout gradient at the native slow radius. -/
theorem CovGSourceGradient {k kc : ℕ} (hk : k + F.N + 2 * F.p ≤ F.Naux)
    (hkc : CovGInputOrder F kc + 1 ≤ k + F.N + 2 * F.p) {c₀ cr Ck Ain : ℝ}
    {Yw : ∀ v : CompIn F.Gr.comps, ℝ → TorusHk (F.Naux + 1) (hr v.1.root)}
    (cl : FullLiftClauses law F.G F.Gr F.m F.p F.Naux F.N F.depth F.sX F.sZ k hk F.η₀ c₀ cr
      F.tp F.tf Ck Ain F.Y Yw)
    (hp : RetainedPair F Yw) (g : CovGNativeWindow F law)
    (hCk : 0 ≤ Ck) (hAin : 0 ≤ Ain) (hcr : 0 < cr) (hcr1 : cr ≤ 1) :
    HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root)
      (CovGInputOrder F kc) (Set.Icc F.tp F.tf) (D.κ (F.m - 1)) (fRho F) (F.G.mass law)
      (fun v t y => toFluxL (gradE (fun z => F.aZ t z v) y))
      (((cr⁻¹) ^ (k + F.N + 2 * F.p) * Ck * Ain) / D.κ (F.m - 1)) := by
  have hE := Z_strongEnergy_liftLength_le F law hk cl hp hcr hcr1 g.mass_pos
  rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hcr.le) _)] at hE
  have he : cr⁻¹ ^ (k + F.N + 2 * F.p) * (Ck * Ain) =
      cr⁻¹ ^ (k + F.N + 2 * F.p) * Ck * Ain := by ring
  rw [he] at hE
  refine EntryTerminal.CovGrad.covGrad_hasFluxBound_of_strongEnergy hkc (F.G.mass law)
    g.B_pos (mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hcr.le) _) hCk) hAin)
    g.mass_pos (ReadoutZ F hk) (ReadoutZw F Yw hk) F.aZ
    (fun v => ReadoutZw_memLp F hp hk v) (fun v => ReadoutZw_ae F hp hk v) ?_ hE
  intro v t ht
  have h1 : 1 ≤ F.Naux := by omega
  exact classicalRep_truncate hk (by omega) _ _ (classicalRep_order_mono _ _ (F.readout v t ht) h1)

private theorem input_floor' {r₀ D₀ H J N p Acl Lc Naux : ℕ}
    (h : succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux) :
    succKc r₀ D₀ H J N p Acl + 6 * p + N + succSchedD D₀ N p (H + 1) + 3 ≤ Naux := by
  have h1 := wKcFloor_le (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl
  have h2 := le_max_left (succSchedD D₀ N p (H + 1) + Lc + N + 6 * p + 4)
    ((succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) + 2 * p)
  simp only [succReconFloor] at h
  dsimp [succKc]
  omega

private theorem reference_prefix (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ)
      (fun Λ _φ₀ _hφ₀ _bw _Q _T₀ _Ce _τe _kS _r₀ _D₀ _H _J _N _p _nk _Lc _Lf _Lpr _Acl
        _Naux _Nout _Kres _npad _sX _sZ _σ₀ _a _σ _kI _CI _Cw _j₀ _CQ _Cpr Cn =>
        0 ≤ Cn ∧ ∀ (D : OCData) (M m : ℕ), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
          IsOCBandChain α q Λ ζ M D.κ → 2 ≤ m → m ≤ M →
            (∀ t, ∑ jl : Fin 2 × Fin 2, |covGradN D m t jl.1 jl.2| ≤ Cn * D.κ (m - 1)) ∧
              Continuous (covGradN D m)) := by
  refine SuccPrefix.of_scale (covGradN_ledger hα₀ hα₁ hs₀ hs₁ hq hζ) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ _hfacts htail CQ Cpr
  exact htail

/-- Either diagonal or inherited mean at every bill context, with the shared native input
as its sole conditional ingredient. The readout energy, covariance size and ledger are proved. -/
theorem CovGPart_of_inputs (diagonal : Bool) (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hin : CovGInputsStatement α s q ζ) :
    CovGPartStatement α s q ζ (if diagonal then 3 else 4) := by
  have hfl := succPrefix_fullLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p _ _ _ _ Acl _ _ _ _ _ _ =>
      succKc r₀ D₀ H J N p Acl + 4 * p + succSchedD D₀ N p (H + 1) + 3)
  have hsize := succPrefix_covSize α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ => 1) (fun _ _ _ _ => one_pos)
  have hled := reference_prefix α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine (((hin.and hfl).and hsize).and hled).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨⟨hinput, henergy⟩, hcov⟩, hCn, hledger⟩ := hx
  let kc := succKc r₀ D₀ H J N p Acl
  let Dm := succSchedD D₀ N p (H + 1)
  let depth := succSchedR r₀ J H
  let K := kc + 4 * p
  let Kin := kc + 6 * p + N + Dm
  let Cletter := CycleComparison.Lift.ambientMeanGradeConstant (wKlift Dm depth N Acl K) N
    (wLlift Dm depth N K) (wLlift Dm depth N K) Dm depth x.1.1.1.CG x.1.1.1.CW
      (fun _ _ => x.1.1.1.Ca)
  let Cnative := max (covTruncGradientCoefficientConst K (N + Dm) *
    CovGNativeCEConst N Dm K Cletter *
      ∑ hh ∈ CovGRawGrades depth diagonal, CI ^ hh) 0
  let Cgrad := kI.cr⁻¹ ^ (Kin + 3) * max x.1.1.2.1 0
  let Ccov := covPolyConst (4 * (Kin : ℝ) ^ 2) p
  let Ctotal := (Cnative + (x.2 + 2)) * (Ccov * Cgrad)
  refine ⟨(Ctotal, max (max (max x.1.1.1.mStar x.1.1.2.2) x.1.2) 2), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  let F := c.frame CcT PZ aRep û hlift aZ aY hZ hY
  have hFp : F.p = p := rfl
  have hFN : F.N = N := rfl
  have hFaux : F.Naux = Naux := rfl
  obtain ⟨⟨g⟩, ⟨hA⟩, hfamily, ⟨pulses⟩⟩ :=
    hinput c (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hm)
      hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have horder := input_floor' hfacts.recon
  have hk : kc + 4 * p + Dm + 3 + N + 2 * p ≤ Naux := by
    dsimp [kc, Dm] at ⊢; omega
  have hAin : 0 ≤ c.Ain := le_trans (Real.sqrt_nonneg _) c.hf
  have cl := billCtx_fullLiftClauses_mono (Ck' := max x.1.1.2.1 0) (le_max_left _ _) hAin
    (henergy hk c (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hm))
  obtain ⟨thr, hKI⟩ := hfacts.admissible
  have hcrEq : kI.cr = kS.cr :=
    (Construction.Preservation.Buffer.invariantAdmissible_molecular_parameters hKI).2.1
  have hcr : 0 < kI.cr := hcrEq ▸ hfacts.hcr
  have hcr1 : kI.cr ≤ 1 := hcrEq ▸ hfacts.hcr_le
  have hgrad := CovGSourceGradient F c.law (kc := kc) hk
    (by rw [CovGInputOrder, hFp, hFN]; dsimp [kc, Dm]; omega)
    cl (retainedPair_of_isRegSolution F c.hsol) g (le_max_right _ _) hAin hcr hcr1
  have hL : kc + 4 * p + Dm + 3 + N + 2 * p = Kin + 3 := by dsimp [Kin]; omega
  rw [hFp, hFN, hL] at hgrad
  have hgrad' : HasFluxBound (h := fun v : CompIn F.G.comps => hr v.1.root)
      (CovGInputOrder F kc) (Set.Icc F.tp F.tf) (c.D.κ (F.m - 1)) (fRho F) (F.G.mass c.law)
      (fun v t y => toFluxL (gradE (fun z => F.aZ t z v) y))
      (Cgrad * c.Ain / c.D.κ (F.m - 1)) := hgrad
  have hs := hcov c (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm)
    CcT PZ aRep û hlift aZ aY hZ hY
  have hsSlow : CovSizeForm F.Mn c.D F.m F.tp F.tf (fRho F) (frameOmega F 1) := by
    change CovSizeForm F.Mn c.D F.m F.tp F.tf (rhoEnh c.D 1 F.m) (frameOmega F 1) at hs
    simpa only [rhoEnh, one_mul, fRho] using hs
  have hs' : CovSizeForm F.Mn c.D F.m F.tp F.tf (fRho F) 1 :=
    ⟨fun t ht => (hsSlow.1 t ht).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsSlow.2.2.1 (sq_nonneg (fRho F))),
      zero_le_one, le_rfl, hsSlow.2.2.2⟩
  have ho : CovGInputOrder F kc + 1 ≤ F.Naux := by
    rw [CovGInputOrder, hFp, hFN, hFaux]; dsimp [kc, Dm]; omega
  have hfilt := CovGFilteredGradient F c.law kc g ho hs' hgrad'
  have he : Ccov * (Cgrad * c.Ain / c.D.κ (F.m - 1)) =
      (Ccov * Cgrad * c.Ain) / c.D.κ (F.m - 1) := by ring
  change HasFluxBound _ _ _ _ _ _ (Ccov * (Cgrad * c.Ain / c.D.κ (F.m - 1))) at hfilt
  rw [he] at hfilt
  have hN : 1 ≤ F.N := le_trans (by norm_num) (succSchedule_two_le_N hfacts.sched)
  have hDm : 1 ≤ Dm := le_trans (by norm_num)
    (Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H)
  obtain ⟨CIthr, Cwthr, hledgerAdm⟩ := hfacts.ledger
  have hSb : 0 ≤ CI := le_trans (by norm_num) (hfacts.hCe.trans hledgerAdm.1)
  have hK : kc + 4 * F.p ≤ wKlift Dm F.depth F.N Acl K + 1 := by
    rw [hFp]; dsimp [K]; unfold wKlift wKmax; omega
  have hprice : CovGRawPrice F diagonal kc Acl K x.1.1.1.CG x.1.1.1.CW x.1.1.1.Ca CI ≤
      Cnative := le_max_left _ _
  have hm2 : 2 ≤ c.m := le_trans (le_max_right _ _) hm
  obtain ⟨hb, hc⟩ := hledger c.D c.M c.m c.hα c.hq c.hΛ c.hζ c.hband hm2 c.m_le_M
  have hJ := CovGReferenceMatrix F x.2 hCn g.B_pos hc hb
  cases diagonal
  · have hmflux := CovGMean_bound F c.law pulses hA g kc hN hDm hfamily hSb hK ho
      (le_max_right _ _) hprice hcr hcr1 hfilt
    simp only [Bool.false_eq_true, ↓reduceIte, CovGFrameAt, show (4 : Fin 5) ≠ 0 by decide,
      show (4 : Fin 5) ≠ 1 by decide, show (4 : Fin 5) ≠ 2 by decide, show (4 : Fin 5) ≠ 3 by decide]
    refine hasFluxBound_mono_Y hmflux ?_
    have hCC : 0 ≤ Ccov := by
      dsimp [Ccov]; unfold covPolyConst
      exact Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg (by positivity) l) (Nat.cast_nonneg _)
    have hCG : 0 ≤ Cgrad := mul_nonneg (pow_nonneg (inv_nonneg.mpr hcr.le) _) (le_max_right _ _)
    dsimp [Ctotal]
    have he : Cnative * (Ccov * Cgrad * c.Ain) = Cnative * (Ccov * Cgrad) * c.Ain := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hJ.2.1) (mul_nonneg hCC hCG)) hAin
  · have hdflux := CovGDiag_bound F c.law pulses hA g kc hN hDm hfamily hSb hK ho
      (le_max_right _ _) hprice hcr hcr1 hJ hfilt
    simp only [↓reduceIte, CovGFrameAt, show (3 : Fin 5) ≠ 0 by decide,
      show (3 : Fin 5) ≠ 1 by decide, show (3 : Fin 5) ≠ 2 by decide]
    convert hdflux using 1
    dsimp [Ctotal]; ring

/-- Part 3: the exact diagonal flux at every bill context; all inputs discharged. -/
theorem covGPart3 (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : CovGPartStatement α s q ζ 3 :=
  CovGPart_of_inputs true α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (covGInputs α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- Part 4: the exact inherited mean flux at every bill context; all inputs discharged. -/
theorem covGPart4 (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : CovGPartStatement α s q ζ 4 :=
  CovGPart_of_inputs false α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (covGInputs α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- The full G form with the energy parts discharged; only the spatial regularity ingredient remains conditional. -/
theorem succPrefix_covGForm_of_regularity (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hreg : CovGPartStatement α s q ζ 1) :
    CovGPartStatement α s q ζ 0 :=
  succPrefix_covGForm_of_ingredients α s q ζ hq hζ hreg
    (covGPart2 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (covGPart3 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (covGPart4 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- **The full covariance G form** at every bill context, with all four
physical ingredients proved and no remaining conditional input. -/
theorem succPrefix_covGForm (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : CovGPartStatement α s q ζ 0 :=
  succPrefix_covGForm_of_regularity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (covGPart1 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation
open AVRegularity.Construction.Preservation.Assembly AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.RetainedEnergy
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The inputs of the filter-defect form at every context, in the common prefix.**

`FilterInputsCtxAt … n L_c Γ' m_*`: at every context of level `≥ m_*`, (R) the regularity of
the coefficients of the full successor at the order `n`, (S) the Schur bound `1/8` of its root
coefficients, (SM) the smoothness of its coefficients, the kernels of `G'` (admissible at
`(Γ', L_c)`, positive width at most `ε_o ρ`), and `ε_o ≤ 1`.

* `filterInputs_at_ctx`: from the constants chosen before the stage.
* `succPrefix_w31FilterInputs`: in the common prefix, at the order `n = k_c + 2p`
  (`k_c = succKc`); the constants are `(Γ', m_*)`. The library statements are those of the
  frontier grade rows (`grade_rows_production`) and `successorKernels`.

The degenerate cases are included: `L_c = 0`; a context of level exactly `m_*`. -/

/-- **The inputs of the filter-defect form at every context of level `≥ m_*`.** -/
def FilterInputsCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (n Lc : ℕ) (Γ' : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    CoeffReg c.G' c.tp c.tf (rhoEnh c.D kI.cr c.m) n ∧
    SchurBound (1 / 8) (kernelSchurMatrix (G := fun _ j _ => hr j.1.root) (c.D.κ (c.m - 1))
      (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) n (succSchedD D₀ N p (H + 1)) c.tp c.tf
      (fun _ => 1)
      (fun v u γ => (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
        c.seedK c.freshK v u γ).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
      (filtCoeff c.G' (fun _ u _ => u.1 ∈ c.G.comps))) ∧
    (∀ (v u : CompIn c.G'.comps) (γ : c.G'.fam.Γ v u) (d : ℕ) (t : ℝ),
      ContDiff ℝ (n : ℕ) (c.G'.physCoeff v u γ d t) ∧ IsZ2Periodic (c.G'.physCoeff v u γ d t)) ∧
    (∀ v u (γ : c.G'.fam.Γ v u),
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).IsAdmissible Γ' Lc ∧
      0 < (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width ∧
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width ≤ FilterBase c.D c.G c.m kI.cr σ₀ * rhoEnh c.D kI.cr c.m) ∧
    FilterBase c.D c.G c.m kI.cr σ₀ ≤ 1

section Ctx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]

/-- **The inputs at a context**, from the constants chosen before the stage. -/
theorem filterInputs_at_ctx (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ)
    (h128 : 128 ≤ Λ) (hbw : 0 < bw)
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr)
    (hprod : kI.Hprod = kI.G0 + H + 1) (hc0pos : 0 < kI.c₀) (hc0le : kI.c₀ ≤ 1)
    (hcrpos : 0 < kI.cr) (hcrle : kI.cr ≤ 1) (hσ₀ : 0 ≤ σ₀)
    (mc : ℕ) (hcert : Frontier.ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p
      nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (Λl : ℕ) (hlength : UniformRecordLengths α q ζ Λl) (hΛl : Λl ≤ Λ)
    (mr : ℕ) (hradius : EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr)
    (Cu : ℝ) (hscale : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu)
    (n : ℕ) (A : ℝ) (mo : ℕ)
    (hop : NativeKernelOperatorsAt α q ζ Λ bw n (succSchedD D₀ N p (H + 1))
      (fun j => max 1 (kI.cker j)) A mo)
    (ma : ℕ)
    (habs : ∀ m, ma ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8)
    {Γk : ℝ} {mk : ℕ} (hkern : KernelsAt α q ζ Λ Γk mk) {Lc : ℕ} (hLker : Lc ≤ kI.Lker)
    (hLnk : kI.Lker + 1 ≤ 2 * nk) (mw : ℕ)
    (hmw : ∀ m, mw ≤ m → 8 * (kI.Cwid * ocEpsilon q Λ (m - 1) ^ kI.lamC) < 1 / 8)
    (hm : max (max mc (max mr (max (mo + 3) (max ma (j₀ + 3))))) (max mk (mw + 1)) ≤ c.m) :
    CoeffReg c.G' c.tp c.tf (rhoEnh c.D kI.cr c.m) n ∧
    SchurBound (1 / 8) (kernelSchurMatrix (G := fun _ j _ => hr j.1.root) (c.D.κ (c.m - 1))
      (rhoEnh c.D kI.cr c.m) (c.G'.mass c.law) n (succSchedD D₀ N p (H + 1)) c.tp c.tf
      (fun _ => 1)
      (fun v u γ => (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
        c.seedK c.freshK v u γ).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
      (filtCoeff c.G' (fun _ u _ => u.1 ∈ c.G.comps))) ∧
    (∀ (v u : CompIn c.G'.comps) (γ : c.G'.fam.Γ v u) (d : ℕ) (t : ℝ),
      ContDiff ℝ (n : ℕ) (c.G'.physCoeff v u γ d t) ∧ IsZ2Periodic (c.G'.physCoeff v u γ d t)) ∧
    (∀ v u (γ : c.G'.fam.Γ v u),
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).IsAdmissible (max kI.Γk (max Γk 2)) Lc ∧
      0 < (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width ∧
      (c.G'.kernelOf (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        v u γ).width ≤ FilterBase c.D c.G c.m kI.cr σ₀ * rhoEnh c.D kI.cr c.m) ∧
    FilterBase c.D c.G c.m kI.cr σ₀ ≤ 1 := by
  have hm1 := le_trans (le_max_left _ _) hm
  have hm2 := le_trans (le_max_right _ _) hm
  have hS := filterSchur_at_ctx hq hζ h128 c hprod hc0pos hc0le hcrpos hcrle mc hcert Λl
    hlength hΛl mr hradius Cu hscale n A mo hop ma habs hm1
  have hK := filterKernels_at_ctx hq.1 h128 hζ c hcrpos hσ₀ hkern hLker hLnk mw hmw hm2
  have hsm := filterCoeffSmooth_at_ctx h128 hbw c hprod mc hcert
    (max_le (le_trans (le_max_left _ _) hm1)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hm1))))) n
  exact ⟨hS.1, hS.2, hsm, hK.1, hK.2⟩

end Ctx

/-- **The inputs of the filter-defect form in the common prefix**, at the order `k_c + 2p`. -/
theorem succPrefix_w31FilterInputs (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 ≤ x.1 ∧
        FilterInputsCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
          σ₀ kI CI Cw j₀ CQ Cpr Q T₀ (succKc r₀ D₀ H J N p Acl + 2 * p) Lc x.1 x.2) := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := Frontier.extended_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  change UniformRecordLengths α q ζ Λl at hlength
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Cu, _hCu, Λp, hΛp, hscale⟩ := AVRegularity.Providers.CascadeInvariants.exists_passScales
    hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λk, hΛk, hkern⟩ := successorKernels α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨max Λc (max Λl (max Λr (max Λp Λk))), by omega, fun Λ hΛ => ?_⟩
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨Γk, -, mk, -, hkern⟩ := hkern Λ (by omega)
  change KernelsAt α q ζ Λ Γk mk at hkern
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ (by omega)
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout _hrecon halloc hsX hsZ
  obtain ⟨tc, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨tc, CH, Υ, hCH, hΥ, fun kI hkI => ?_⟩
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, fun CI Cw j₀ hledger hstart CQ Cpr => ?_⟩
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hledger hstart
  change Frontier.ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
    σ₀ kI CI Cw j₀ mc at hc
  obtain ⟨hc0I, hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hc0pos : 0 < kI.c₀ := hc0I.symm ▸ hc₀
  have hc0le : kI.c₀ ≤ 1 := hc0I.symm ▸ hc₀upper.trans (min_le_right _ _)
  have hcrpos : 0 < kI.cr := hcrI.symm ▸ hcr
  have hcrle : kI.cr ≤ 1 := hcrI.symm ▸ hcrupper
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) := Buffer.preparation_schedule_order_ge_two D₀ N p H
  obtain ⟨mr, _hmr, hradius⟩ := hradius Λ (by omega) kI.c₀ kI.cr hc0pos hcrpos
  change EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr at hradius
  obtain ⟨A, _hA, mo, _hmo, hop⟩ := uniform_native_kernel_operator_of_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw (succKc r₀ D₀ H J N p Acl + 2 * p)
    (succSchedD D₀ N p (H + 1)) hDm (fun j => max 1 (kI.cker j))
    (fun j _ => zero_le_one.trans (le_max_left _ _))
  change NativeKernelOperatorsAt α q ζ Λ bw (succKc r₀ D₀ H J N p Acl + 2 * p)
    (succSchedD D₀ N p (H + 1)) (fun j => max 1 (kI.cker j)) A mo at hop
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < min (ocDelta α q / 4) τe := lt_min (div_pos hδ (by norm_num)) hτe
  obtain ⟨ma, habs⟩ := retained_absorption_threshold hq.1 h128 hτ A CI
  have hσ₀ : 0 < σ₀ := by
    obtain ⟨_, _, _, _, _, hsum, ha, has, _⟩ := hsched
    linarith only [hsum, ha, has]
  have hlam : 0 < kI.lamC := hσ₀.trans hkI.2.2.2.2.2.2.2.1
  obtain ⟨mw, hmw⟩ := retained_absorption_threshold hq.1 h128 hlam 8 kI.Cwid
  have hscale' : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu := by
    intro D hDα hDq hDΛ hDζ hband m hm hmM
    apply hscale D hDα hDq hDζ (by omega) _ m hm hmM
    simpa only [hDα, hDq, hDζ] using hband
  have hLker : Lc ≤ kI.Lker := le_trans (le_trans (le_max_left Lc Lf) (le_max_right Lpr _))
    hkI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLnk : kI.Lker + 1 ≤ 2 * nk := hkI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨(max kI.Γk (max Γk 2),
    max (max mc (max mr (max (mo + 3) (max ma (j₀ + 3))))) (max mk (mw + 1))),
    le_trans zero_le_two (le_trans (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm
  exact filterInputs_at_ctx hq hζ h128 hbw c hprod hc0pos hc0le hcrpos hcrle hσ₀.le mc hc Λl
    hlength (by omega) mr hradius Cu hscale' _ A mo hop ma habs hkern hLker hLnk mw hmw hm

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The filter-defect form at every context.**

`FilterFormCtxAt … k_c L_c C m_*`: at every context of level `≥ m_*`, for every classical
representative `a_Z` of the readout of the retained solution (order `N_aux`),
`FilterDefectForm … (C · succFilterPrice … · A_in)` at the radius `rhoEnh D c_r m`, the masses of
`G` and the coarse order `k_c`: the second hypothesis of `frameFilter_of_forms`, in the frame
form of the consumer.

`succPrefix_w31FilterForm`: in the common prefix at `k_c = succKc`, with `0 ≤ C`. The inputs are
`succPrefix_w31FilterInputs` (R, S, SM, kernels, `ε_o ≤ 1`) and `succPrefix_fullLift` at the
order `k_c + 2p + (D_m - 2) + L_c` (EN); the orders fit by `fluxOrders_of_succReconFloor`.
The constant is `C = √(|W_{J+1}| + 1) M_c (1/8) max(C_k, 0)`.

The degenerate cases are included: `L_c = 0` (the price is `1`); `A_in = 0` (the bound is `0`). -/

/-- The full-lift clauses with a nonnegative constant. -/
theorem fullLiftClauses_mono {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {law : BirthLaw} {G Gr : GenStage D hr Dm b j₀}
    {m p Naux N depth sX sZ k : ℕ} {hk : k + N + 2 * p ≤ Naux} {η₀ c₀ cr tp tf Ck Ain : ℝ}
    {Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root)}
    {Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)}
    (h : FullLiftClauses law G Gr m p Naux N depth sX sZ k hk η₀ c₀ cr tp tf Ck Ain Y Yw)
    (hA : 0 ≤ Ain) :
    FullLiftClauses law G Gr m p Naux N depth sX sZ k hk η₀ c₀ cr tp tf (max Ck 0) Ain Y Yw := by
  refine ⟨h.1, fun CcT PZ aRep û ŵ hW w hw => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 CcT PZ aRep û ŵ hW w hw
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      (by positivity)),
    h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hA))⟩

/-- **The filter-defect form at every context of level `≥ m_*`.** -/
def FilterFormCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (kc Lc : ℕ) (C : ℝ) (mStar : ℕ) :
    Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root,
      (∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux) →
      FilterDefectForm (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        φ₀ c.G c.G' c.m p kc (c.D.eps (c.m - 1)) (succEta0 α q s) aZ (c.G.mass c.law) c.tp c.tf
        (rhoEnh c.D kI.cr c.m) (C * succFilterPrice c.D c.G c.m kI.cr σ₀ Lc * c.Ain)

/-- **The filter-defect form in the common prefix form**: the constants are `(C, m_*)` with
`0 ≤ C`. -/
theorem succPrefix_w31FilterForm (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 ≤ x.1 ∧
        FilterFormCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
          σ₀ kI CI Cw j₀ CQ Cpr Q T₀ (succKc r₀ D₀ H J N p Acl) Lc x.1 x.2) := by
  have h1 := succPrefix_fullLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun r₀ D₀ H J N p _ Lc _ _ Acl _ _ _ _ _ _ =>
      succKc r₀ D₀ H J N p Acl + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc)
  have h2 := succPrefix_w31FilterInputs α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨hfl, hΓ', hin⟩ := hx
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcr : 0 < kI.cr := by rw [hkI.2.1]; exact hfacts.hcr
  have hη := FullLift.successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq
  have hD2 : 2 ≤ succSchedD D₀ N p (H + 1) := Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hN2 : 2 ≤ N := succSchedule_two_le_N hfacts.sched
  have horders : succKc r₀ D₀ H J N p Acl + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc + 1 +
      N + 2 * p ≤ Naux := (fluxOrders_of_succReconFloor hfacts.recon).2.2
  have hk : succKc r₀ D₀ H J N p Acl + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc + N + 2 * p ≤
      Naux := by omega
  have hNaux : succKc r₀ D₀ H J N p Acl + 2 * p + succSchedD D₀ N p (H + 1) ≤ Naux := by omega
  have hKN : succKc r₀ D₀ H J N p Acl + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc + 1 ≤
      Naux := by omega
  have hMc : 0 ≤ FilterMc φ₀ Lc (succKc r₀ D₀ H J N p Acl + 2 * p)
      (succSchedD D₀ N p (H + 1)) x.2.1 := FilterMc_nonneg _ _ _ _ hΓ'
  refine ⟨(Real.sqrt (((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) + 1) *
      (FilterMc φ₀ Lc (succKc r₀ D₀ H J N p Acl + 2 * p) (succSchedD D₀ N p (H + 1)) x.2.1 *
        (1 / 8) * max x.1.1 0), max x.1.2 (max x.2.2 1)), ?_, ?_⟩
  · have := le_max_right x.1.1 0
    positivity
  intro hr _ _ _ _ _ _ _ c hm aZ hZ
  have hm1 : x.1.2 ≤ c.m := le_trans (le_max_left _ _) hm
  have hm2 : x.2.2 ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm3 : 1 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hA : 0 ≤ c.Ain := le_trans (by unfold weightedNorm; exact Real.sqrt_nonneg _) c.hf
  have hfl' := fullLiftClauses_mono (hfl hk c hm1) hA
  obtain ⟨hreg, hS, hsm, hker, hbase⟩ := hin c hm2
  have hEn := filterEnergy_at_ctx c hk hfl' aZ hZ
    (c.kappa_pred_pos (le_trans (by norm_num) hfacts.hΛ) hζ)
    (c.mass_pos hq.1 hfacts.hΛ) (mul_nonneg (le_max_right _ _) hA)
    (K := succKc r₀ D₀ H J N p Acl + 2 * p + (succSchedD D₀ N p (H + 1) - 2) + Lc)
    (by omega) hKN
  have hF := filterForm_at_ctx hη hq.1 hfacts.hΛ hζ hcr hfacts.smooth hfacts.nonneg
    hfacts.mass hfacts.support c hm3 aZ hZ hNaux hΓ' hreg hS hsm hker hbase hEn
  refine filterDefectForm_mono hF (le_of_eq ?_)
  rw [FilterBase_pow]
  ring

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The bounds of the residual at every context** (cascade side of the bill residual).

`succPrefix_residualBound`: in the common prefix form, constants `(C, c_g, m_*)` with `c_g > 0`
such that at every context of level `≥ m_*`, under the quiet margin of the preparation endpoint, at the
frame `F` of every lifted field with classical representatives for which the coarse equation of
`P_pZ` holds (`F.macroWeak`) and the lifted classical field is jointly measurable on the window,
the bounds of the residual hold with the bill `C·𝔅·A_in` (`FrameResidualBoundAt`).

Inputs proved here: the covariance size form (`succPrefix_covSize` at the radius factor `k_I.c_r`), the covariance gradient form
(`succPrefix_covGrad`), the reconstruction bound on a nondegenerate window (`succPrefix_recon`)
and on a degenerate one (`succPrefix_reconDegenerate`), the fine tail bound (`succPrefix_fineTail`), the generic operators
(`covTruncOp`, `covTruncSub`, `filterPOp`) and the word conversion (`residualWordsOfMass`).
Inputs from other trees, as hypotheses: the covariance G form (`CovGCtxAt`), the frontier inner flux
(`FrontierInnerPrefixStatement`), the filter defect (`FilterDefectCtxAt`), the coarse reconstruction
(`ReconCoarseCtxAt`, from the reconstruction letters and the reconstruction defect by `succPrefix_reconCoarse_of_parts`).

The constants: `C₁ = max(C_G, C_∇, 0)`, `C₂ = max(C_B, 0)`, `C₃ = max(C_F, 0)`,
`C_fl = max(C_op C₁ + C₁, C_P C₂, C_P' C₃)`, `C_c = max(C_rec(C_fl), C_fine, 0)`, `C = 3·0!·C_c`.

The case `t_p = t_f` is the degenerate reconstruction; `A_in = 0` is allowed. -/

/-- **The bounds of the residual at every context of level `≥ m_*`.** -/
def ResidualBoundCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Lc Lf Acl : ℕ) (cg C : ℝ)
    (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      (c.frame CcT PZ aRep û hlift aZ aY hZ hY).macroWeak →
      (∀ v : CompIn c.G.comps, Measurable
        (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc c.tp c.tf} =>
          (c.frame CcT PZ aRep û hlift aZ aY hZ hY).uh z.1.1 z.1.2 v)) →
      FrameResidualBoundAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law kI.c₀ kI.cr cg σ₀ Lc
        Lf Acl
        (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H))
        c.Ain C

/-- **The bounds of the residual in the common prefix form**, from the inputs of the other
trees; the constants are `(C, c_g, m_*)` with `0 < c_g`. -/
theorem succPrefix_residualBound (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hG : SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        CovGCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2))
    (hB : FrontierInnerPrefixStatement α s q ζ)
    (hF : SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FilterDefectCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl Lc x.1 x.2))
    (hR5 : SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconCoarseCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl Lc x)) :
    SuccPrefix α s q (X := ℝ × ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 < x.2.1 ∧ ResidualBoundCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad
          sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Lc Lf Acl x.2.1 x.1 x.2.2) := by
  have h1 := succPrefix_covSize α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ (fun _ kI => kI.cr)
    (fun _ _ h e => e ▸ h)
  have h2 := succPrefix_covGrad α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h3 := succPrefix_recon α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h4 := succPrefix_reconDegenerate α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h5 := succPrefix_fineTail α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ((((((((h1.and hG).and h2).and hB).and hF).and h3).and h4).and h5).and hR5).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨x1, xG⟩, xgr⟩, xB⟩, xF⟩, xR⟩, xdeg⟩, xfine⟩, xr5⟩ := x
  obtain ⟨CGl, Cwl, Ca, Cgr, cg, Cfun, mR⟩ := xR
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hS, hGx⟩, hgr⟩, ⟨hB0, hBx⟩⟩, hFx⟩, ⟨-, hcg, hrec⟩⟩, hdeg⟩, hfine⟩, hr5⟩ := hx
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcr : 0 < kI.cr := by rw [hkI.2.1]; exact hfacts.hcr
  have hc₀ : 0 < kI.c₀ := by rw [hkI.1]; exact hfacts.hc₀
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hW := (windowOrders_of_succReconFloor hfacts.recon).1
  obtain ⟨Cop, hCop, hcov⟩ := frameCovTrunc_of_forms covTruncOp covTruncSub
    (succKc r₀ D₀ H J N p Acl) p
  obtain ⟨Cpf, hCpf, hfro⟩ := frameFrontier_of_forms filterPOp (succKc r₀ D₀ H J N p Acl) p
  obtain ⟨Cpi, hCpi, hfil⟩ := frameFilter_of_forms filterPOp (succKc r₀ D₀ H J N p Acl) p
  -- the constants
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = max (max xG.1 xgr.1) 0 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = max xB.1 0 := ⟨_, rfl⟩
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = max xF.1 0 := ⟨_, rfl⟩
  obtain ⟨Cfl, hCfl⟩ : ∃ Cfl : ℝ, Cfl = max (max (Cop * C₁ + C₁) (Cpf * C₂)) (Cpi * C₃) :=
    ⟨_, rfl⟩
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = max (max (Cfun Cfl) xfine.1) 0 := ⟨_, rfl⟩
  have hC₁G : xG.1 ≤ C₁ := hC₁ ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hC₁g : xgr.1 ≤ C₁ := hC₁ ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hC₁0 : 0 ≤ C₁ := hC₁ ▸ le_max_right _ _
  have hC₂B : xB.1 ≤ C₂ := hC₂ ▸ le_max_left _ _
  have hC₂0 : 0 ≤ C₂ := hC₂ ▸ le_max_right _ _
  have hC₃F : xF.1 ≤ C₃ := hC₃ ▸ le_max_left _ _
  have hC₃0 : 0 ≤ C₃ := hC₃ ▸ le_max_right _ _
  have hfl1 : Cop * C₁ + C₁ ≤ Cfl := hCfl ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hfl2 : Cpf * C₂ ≤ Cfl := hCfl ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hfl3 : Cpi * C₃ ≤ Cfl := hCfl ▸ le_max_right _ _
  have hCcr : Cfun Cfl ≤ Cc := hCc ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hCcf : xfine.1 ≤ Cc := hCc ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hCc0 : 0 ≤ Cc := hCc ▸ le_max_right _ _
  refine ⟨(3 * ((0 : ℕ).factorial : ℝ) * Cc, cg,
    max (max (max x1 xG.2) (max xgr.2 xB.2)) (max (max xF.2 mR) (max (max xdeg xfine.2) xr5))),
    hcg, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hmacro hmeas
  replace hm : max (max (max x1 xG.2) (max xgr.2 xB.2))
      (max (max xF.2 mR) (max (max xdeg xfine.2) xr5)) ≤ c.m := hm
  have hm1 : x1 ≤ c.m := by omega
  have hm2 : xG.2 ≤ c.m := by omega
  have hm3 : xgr.2 ≤ c.m := by omega
  have hm4 : xB.2 ≤ c.m := by omega
  have hm5 : xF.2 ≤ c.m := by omega
  have hm6 : mR ≤ c.m := by omega
  have hm7 : xdeg ≤ c.m := by omega
  have hm8 : xfine.2 ≤ c.m := by omega
  have hm9 : xr5 ≤ c.m := by omega
  -- the scales of the context
  have hqD : 1 < c.D.q := c.q_gt hq.1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge hfacts.hΛ
  have hE : 0 ≤ c.D.eps (c.m - 1) := (Scales.epsilon_basic (m := c.m - 1) hqD hΛD).1.le
  have he : 0 ≤ c.D.eps c.m := (Scales.epsilon_basic (m := c.m) hqD hΛD).1.le
  have hA : 0 ≤ c.Ain := le_trans (Real.sqrt_nonneg _) c.hf
  have hκ : 0 < c.D.κ (c.m - 1) := c.kappa_pred_pos hΛ1 hζ
  have hρ : 0 < rhoEnh c.D kI.cr c.m :=
    mul_pos hcr (Real.sqrt_pos.2 (mul_pos hκ
      (Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD))))
  have hπ : ∀ v, 0 < c.G.mass c.law v := c.mass_pos hq.1 hfacts.hΛ
  -- the three flux bounds
  have hSx := hS c hm1 CcT PZ aRep û hlift aZ aY hZ hY
  have hω : 0 ≤ frameOmega (c.frame CcT PZ aRep û hlift aZ aY hZ hY) kI.cr := hSx.2.1
  have h2a := hcov (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law rfl kI.cr c.Ain C₁ hκ hρ hπ hA
    hC₁0 hSx
    (covGForm_mono (hGx c hm2 hquietMargin CcT PZ aRep û hlift aZ aY hZ hY)
      (mul_le_mul_of_nonneg_right hC₁G hA))
    (covGradForm_mono (hgr c hm3 CcT PZ aRep û hlift aZ aY hZ hY)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁g (pow_nonneg hω _)) hA))
  have h2b := hfro (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law rfl kI.cr _ _ _ c.Ain C₂ hκ hρ hπ
    hSx
    (frontierInnerForm_mono (hBx c hm4 CcT PZ aRep û hlift aZ aY hZ hY)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂B
        (succFrontPrice_nonneg _ _ _ _ _ hE)) hA))
  have h3 := hfil (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law rfl kI.cr σ₀ Lc _ c.Ain C₃ hκ hρ
    hπ hSx
    (filterDefectForm_mono' (hFx c hm5 hquietMargin CcT PZ aRep û hlift aZ aY hZ hY)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₃F
        (succFilterPrice_nonneg _ _ _ _ hE)) hA))
  -- the reconstruction
  have hrecAt : ∃ Cr, Cr ≤ Cc ∧ FrameReconAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law
      (succKc r₀ D₀ H J N p Acl) kI.c₀ kI.cr cg
      σ₀ Lc Acl (succTheta1 α q s σ₀ (succDstar D₀ N p H))
      (succTheta2 α q s σ₀ (succDstar D₀ N p H)) c.Ain Cfl Cr := by
    rcases lt_or_eq_of_le c.tp_le_tf with htt | htt
    · exact ⟨Cfun Cfl, hCcr, hrec Cfl c hm6 htt hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hW
        (hr5 c hm9 htt hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hmacro hW Cfl CGl Cwl Ca CI Cgr)⟩
    · exact ⟨Cc, le_rfl, hdeg c hm7 htt.symm CcT PZ aRep û hlift aZ aY hZ hY hmeas
        (succKc r₀ D₀ H J N p Acl) cg Cfl Cc hCc0⟩
  obtain ⟨Cr, hCr, hrecC⟩ := hrecAt
  exact frameResidualBound_of_bounds (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law
    residualWordsOfMass hπ hA hE he hcr.le hc₀.le
    hfl1 hfl2 hfl3 hCr hCcf h2a h2b h3 hrecC
    (hfine c hm8 CcT PZ aRep û hlift aZ aY hZ hY hmeas)

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The flux and reconstruction pieces in the context forms of the bill residual** (cascade side of the bill
residual).

* `succPrefix_covGCtx`: the covariance G form (`CovGCtxAt`) from `succPrefix_covGForm` (proved; part 0 of
  `CovGPartStatement`, whose text is `CovGCtxAt`).
* `succPrefix_filterDefectCtx`: the filter defect (`FilterDefectCtxAt`) from `succPrefix_w31FilterForm` (proved; it does not need the quiet margin).
* `succPrefix_reconLettersCtx`: the reconstruction letters (`ReconLettersCtxAt`) from the at-form
  `frameReconLetters` (proved). Its frame hypotheses at the context: the stage invariant
  `c.hinv` on `[t_A, t_f]`, the level, `F.m < D.term` (`c.m_lt_term`), the incoming lift geometry
  (`j₀ ≤ m`, depth, reserves, lengths: `succPrefix_retainedProductionBundle`), `lenFactor = 1` (the cascade
  menu), the entrance `t_A + 3τ_m ≤ t_p` (`c.entrance`), `t_p ≤ t_f` and the quiet margin; its orders
  are `D_m = D_{H+1} ≥ 2`, `N ≥ 1`, `k_c = succKc`.

The case `t_p = t_f` is not asked (`ReconLettersCtxAt` is stated for `t_p < t_f`);
`A_in = 0` is allowed. -/

/-- **The covariance G form at every context** from `succPrefix_covGForm`. -/
theorem succPrefix_covGCtx (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        CovGCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2) := by
  refine (succPrefix_covGForm α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  refine ⟨x, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have h := hx c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  simp only [CovGFrameAt, ↓reduceIte] at h
  exact h

/-- **The filter defect at every context** from `succPrefix_w31FilterForm`. -/
theorem succPrefix_filterDefectCtx (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FilterDefectCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc x.1 x.2) := by
  refine (succPrefix_w31FilterForm α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  exact ⟨x, fun c hm _hquietMargin _CcT _PZ _aRep _û _hlift aZ _aY hZ _hY => hx.2 c hm aZ hZ⟩

/-- The reconstruction letters at every context with the incoming lift geometry as a premise (the form produced from
the at-form before the retained production bundle is joined). -/
def ReconLettersGeomCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ)
    (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m → c.tp < c.tf →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    IncomingLiftGeometryStatement c.G kI (succSchedR r₀ J H) 2 2 →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      FrameReconLettersAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law (succKc r₀ D₀ H J N p Acl)

/-- The letters at every context, before the geometry is joined. -/
theorem succPrefix_reconLettersGeomCtx {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconLettersGeomCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
          σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl x) := by
  refine SuccPrefix.of_scale (frameReconLetters hα₀ hα₁ hs₀ hs₁ hq hζ) ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts hP CQ Cpr
  have hD2 : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hN : 1 ≤ N := le_trans (by norm_num) (succSchedule_two_le_N hfacts.sched)
  obtain ⟨m₁, -, hS⟩ := hP bw hfacts.hbw (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N
    (succKc r₀ D₀ H J N p Acl) hD2 hN
  refine ⟨m₁, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm htt hquietMargin hgeom CcT PZ aRep û hlift aZ aY hZ hY
  obtain ⟨-, -, -, hj, hdepth, hres, hres2, hlen, -, -⟩ := hgeom
  have hj' : j₀ ≤ c.m := c.hlevel ▸ hj
  have hentry : c.tA + 3 * ocTau c.D.α c.D.q c.D.Λ c.m ≤ c.tp := by
    rw [c.hα, c.hq, c.hΛ]
    exact c.entrance
  have hquietMargin' : Set.Icc (c.tp - ocTauP c.D.α c.D.q c.D.Λ c.m)
      (c.tp + ocTauP c.D.α c.D.q c.D.Λ c.m) ⊆ ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ c.m := by
    rw [c.hα, c.hq, c.hΛ, c.hζ]
    exact hquietMargin
  exact hS hr c.D c.hα c.hq c.hΛ c.hζ c.hseq c.bandD j₀ (c.frame CcT PZ aRep û hlift aZ aY hZ hY)
    c.law hφ₀
    c.Mnat kI c.tA c.tf _ _
    c.hinv rfl rfl c.hlevel hm c.m_lt_term hj' hdepth hres hres2 hlen rfl hentry c.tp_le_tf le_rfl
    hquietMargin'

/-- **The reconstruction letters at every context** from the letters and the incoming lift geometry of the
retained production bundle. -/
theorem succPrefix_reconLettersCtx (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconLettersCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ Acl x) := by
  have h1 := succPrefix_reconLettersGeomCtx hα₀ hα₁ hs₀ hs₁ hq hζ
  have h2 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  refine ⟨max x.1 x.2.2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm htt hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  exact hx.1 c (le_trans (le_max_left _ _) hm) htt hquietMargin
    (hx.2.2 hk0 c (le_trans (le_max_right _ _) hm)).1 CcT PZ aRep û hlift aZ aY hZ hY

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
