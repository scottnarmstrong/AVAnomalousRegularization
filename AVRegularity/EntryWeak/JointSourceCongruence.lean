-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.WeakCarrierAppend
public import AVRegularity.EntryWeak.SourceParameterPeriodicity
public import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.ChartIntegrandAlgebra
import AVRegularity.Construction.ChildInert.Center
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Classical.GalerkinGenerator
public import Mathlib.Analysis.Matrix.Normed
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Genuine slow source words are restrictions of finite joint fast and slow words. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jointSlowWord (p : ℕ × ℕ) : Fin (p.1 + p.2) → Vec 2 × Vec 2 :=
  fun i => (0, realParameterCanonicalWord p i)

theorem jointSlowWord_norm_le_one (p : ℕ × ℕ) :
    ∀ i, ‖jointSlowWord p i‖ ≤ 1 := by
  intro i
  simpa only [jointSlowWord, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
    realParameterCanonicalWord_norm_le_one p i

theorem sourceParameterJet_eq_jointWord (f : ℝ → Vec 2 → Vec 2 → E)
    (p : ℕ × ℕ) (hf : ∀ t, ContDiff ℝ ((p.1 + p.2 : ℕ) : ℕ∞)
      (fun X : Vec 2 × Vec 2 => f t X.1 X.2)) (Y : Vec 2) (t : ℝ) (z : Vec 2) :
    sourceParameterJet f p Y t z =
      realWordJet (fun X : Vec 2 × Vec 2 => f t X.1 X.2) (p.1 + p.2)
        (jointSlowWord p) (z, Y) := by
  have he := finite_realWordJet_affine_eq
    (fun X : Vec 2 × Vec 2 => f t X.1 X.2) (p.1 + p.2) (hf t)
    (ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2)) (z, 0)
    (realParameterCanonicalWord p) Y
  change iteratedFDeriv ℝ (p.1 + p.2) (f t z) Y (realParameterCanonicalWord p) =
    iteratedFDeriv ℝ (p.1 + p.2) (fun X : Vec 2 × Vec 2 => f t X.1 X.2) (z, Y)
      (fun i => (0, realParameterCanonicalWord p i))
  simpa only [realWordJet, sourceParameterJet, realParameterCanonicalJet,
    realParameterWordJet, jointSlowWord, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, zero_add, add_zero] using he

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Actual finite slow source jets in the uniformly local forcing norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem finite_sourceParameterJet_measurable (f : ℝ → Vec 2 → Vec 2 → E)
    (p : ℕ × ℕ) (hf : ∀ t z, ContDiff ℝ ((p.1 + p.2 : ℕ) : ℕ∞) (f t z))
    (hm : ∀ Y, Measurable (fun a : ℝ × Vec 2 => f a.1 a.2 Y)) (Y : Vec 2) :
    Measurable (Function.uncurry (sourceParameterJet f p Y)) :=
  finite_realParameterCanonicalJet_measurable (fun a : ℝ × Vec 2 => f a.1 a.2) p
    (fun a => hf a.1 a.2) hm Y

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Actual canonical slow source jets retain the genuine remaining joint derivative reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sourceParameterJet_joint_contDiff (f : ℝ → Vec 2 → Vec 2 → E)
    (p : ℕ × ℕ) (r : ℕ)
    (hf : ∀ t, ContDiff ℝ ((p.1 + p.2 + r : ℕ) : ℕ∞)
      (fun X : Vec 2 × Vec 2 => f t X.1 X.2)) (t : ℝ) :
    ContDiff ℝ (r : ℕ∞)
      (fun X : Vec 2 × Vec 2 => sourceParameterJet f p X.2 t X.1) := by
  have he : (fun X : Vec 2 × Vec 2 => sourceParameterJet f p X.2 t X.1) =
      realWordJet (fun X : Vec 2 × Vec 2 => f t X.1 X.2) (p.1 + p.2) (jointSlowWord p) := by
    funext X
    exact sourceParameterJet_eq_jointWord f p
      (fun s => (hf s).of_le (by exact_mod_cast (show p.1 + p.2 ≤ p.1 + p.2 + r by omega))) X.2 t X.1
  rw [he]
  exact finite_realWordJet_contDiff _ _ r (hf t) _

theorem sourceParameterJet_joint_derivative_bound (f : ℝ → Vec 2 → Vec 2 → E)
    (p : ℕ × ℕ) (r : ℕ)
    (hf : ∀ t, ContDiff ℝ ((p.1 + p.2 + r : ℕ) : ℕ∞)
      (fun X : Vec 2 × Vec 2 => f t X.1 X.2)) (t : ℝ) (X : Vec 2 × Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X : Vec 2 × Vec 2 => sourceParameterJet f p X.2 t X.1) X‖ ≤
      ‖iteratedFDeriv ℝ (p.1 + p.2 + r) (fun X : Vec 2 × Vec 2 => f t X.1 X.2) X‖ := by
  have he : (fun X : Vec 2 × Vec 2 => sourceParameterJet f p X.2 t X.1) =
      realWordJet (fun X : Vec 2 × Vec 2 => f t X.1 X.2) (p.1 + p.2) (jointSlowWord p) := by
    funext Z
    exact sourceParameterJet_eq_jointWord f p
      (fun s => (hf s).of_le (by exact_mod_cast (show p.1 + p.2 ≤ p.1 + p.2 + r by omega))) Z.2 t Z.1
  rw [he]
  exact finite_realWordJet_derivative_bound _ _ r (hf t) _ (jointSlowWord_norm_le_one p) X

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Higher torus curves are strongly measurable from their scalar Hilbert pairings. -/

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace A]

theorem torusHk_stronglyMeasurable_of_pairings (K : ℕ) (f : A → TorusHk K E)
    (hf : ∀ z : TorusHk K E, StronglyMeasurable (fun t => inner ℝ (f t) z)) :
    StronglyMeasurable f := by
  have hproj (N : ℕ) : StronglyMeasurable (fun t => galerkinProj N (f t)) := by
    let R := (galerkinProj (E := E) (K := K) N).toLinearMap.range
    let : FiniteDimensional ℝ R := galerkinProj_range_finite N
    let T : TorusHk K E →L[ℝ] R := (galerkinProj N).codRestrict R (fun u => ⟨u, rfl⟩)
    let basis := Module.finBasis ℝ R
    let L := fun i => (basis.coord i).toContinuousLinearMap.comp T
    have hcoord (i) : StronglyMeasurable (fun t => L i (f t)) := by
      let z := (InnerProductSpace.toDual ℝ (TorusHk K E)).symm (L i)
      have he : (fun t => L i (f t)) = fun t => inner ℝ (f t) z := by
        funext t
        exact ((real_inner_comm _ _).trans InnerProductSpace.toDual_symm_apply).symm
      rw [he]
      exact hf z
    have hsum : StronglyMeasurable (fun t => ∑ i, L i (f t) • basis i) := by
      exact Finset.stronglyMeasurable_fun_sum Finset.univ
        (f := fun i t => L i (f t) • basis i) (fun i _ =>
          (hcoord i).smul (stronglyMeasurable_const (b := basis i)))
    have he : (fun t => ∑ i, L i (f t) • basis i) = fun t => T (f t) := by
      funext t
      exact basis.sum_repr _
    rw [he] at hsum
    exact R.subtypeL.continuous.comp_stronglyMeasurable hsum
  apply stronglyMeasurable_of_tendsto atTop hproj
  exact tendsto_pi_nhds.mpr (fun t => galerkinProj_tendsto (f t))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.WeakUniqueness AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Finite C¹ periodic scalar data give the actual classical first weak jet. -/

theorem classical_first_jet_periodicWeak (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ 1 q) (hp : AVenhance.IsZ2Periodic q) :
    HasPeriodicOrderedWeakJet (cellSmoothScalarJet q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact GalerkinGenerator.classicalWordDerivative_periodic _ q hp
  · intro a
    rcases a with ⟨j, w⟩
    fin_cases j
    · exact weak_continuous_memL2On hq.continuous
    · have hc : Continuous (fun x => fderiv ℝ q x (basisVec (w 0))) :=
        (hq.continuous_fderiv (by simp)).clm_apply continuous_const
      exact weak_continuous_memL2On hc
  · intro j w i e
    fin_cases j
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    have hweak := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i)
      ((contDiff_const : ContDiff ℝ 1 (fun _ : Vec 2 => e)).mul hq)
    have hder (x : Vec 2) : fderiv ℝ (fun y => e * q y) x (basisVec i) =
        e * AVenhance.spaceGrad q x i := by
      rw [fderiv_const_mul (hq.differentiable (by simp) x)]
      rfl
    intro φ hφ hc hs
    change (∫ x in Set.univ, q x * e * fderiv ℝ φ x (basisVec i)) =
      -∫ x in Set.univ, AVenhance.spaceGrad q x i * e * φ x
    simpa only [hder, mul_comm] using hweak φ hφ hc hs

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Jointly measurable literal jets yield strongly measurable Sobolev carriers. -/

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace A]

theorem torusHk_stronglyMeasurable_of_raw_jets (K : ℕ)
    (w : A → TorusHk K E) (F : A → RawJet2 K E)
    (hm : ∀ a, Measurable (fun p : A × Vec 2 => F p.1 a p.2))
    (he : ∀ t a, (w t).val a =ᵐ[volume.restrict AVenhance.unitCube] F t a) :
    StronglyMeasurable w := by
  apply torusHk_stronglyMeasurable_of_pairings K w
  intro z
  have hi (a : JetIndex2 K) : StronglyMeasurable (fun t =>
      ∫ x in AVenhance.unitCube, inner ℝ (F t a x) (z.val a x)) := by
    have hz : StronglyMeasurable (fun p : A × Vec 2 => z.val a p.2) :=
      (Lp.stronglyMeasurable (z.val a)).comp_measurable measurable_snd
    exact ((hm a).stronglyMeasurable.inner hz).integral_prod_right
  have hs : StronglyMeasurable (fun t => ∑ a : JetIndex2 K,
      ∫ x in AVenhance.unitCube, inner ℝ (F t a x) (z.val a x)) := by
    exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun a _ => hi a)
  have heq : (fun t => ∑ a : JetIndex2 K,
      ∫ x in AVenhance.unitCube, inner ℝ (F t a x) (z.val a x)) =
      (fun t => inner ℝ (w t) z) := by
    funext t
    change (∑ a, ∫ x in AVenhance.unitCube, inner ℝ (F t a x) (z.val a x)) =
    inner ℝ (w t).val z.val
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he t a] with x hx
    rw [hx]
  rw [← heq]
  exact hs

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.EntryWeakProofs

/-! Classical finite spatial regularity supplies the full ordered Sobolev jet. -/

theorem classicalWordDerivative_contDiff_finite (w : List (Fin 2)) (n : ℕ)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ ((n + w.length : ℕ) : ℕ∞) q) :
    ContDiff ℝ (n : ℕ∞) (classicalWordDerivative w q) := by
  induction w generalizing n with
  | nil => simpa [classicalWordDerivative] using hq
  | cons i w ih =>
    have hw : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (classicalWordDerivative w q) :=
      ih (n + 1) (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hq)
    change ContDiff ℝ (n : ℕ∞)
      (fun x => fderiv ℝ (classicalWordDerivative w q) x (basisVec i))
    exact (hw.fderiv_right (by simp)).clm_apply contDiff_const

theorem smoothLiftWord_length (n : ℕ) (w : DerivativeWord2 n) :
    (smoothLiftWord n w).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [smoothLiftWord, ih]

def classicalFiniteJet (l : ℕ) (q : Vec 2 → ℝ) : RawJet2 l ℝ :=
  fun a => classicalWordDerivative (smoothLiftWord a.1.val a.2) q

theorem classicalFiniteJet_continuous (l : ℕ) (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (l : ℕ∞) q) (a : JetIndex2 l) :
    Continuous (classicalFiniteJet l q a) := by
  apply (classicalWordDerivative_contDiff_finite (smoothLiftWord a.1.val a.2) 0 q ?_).continuous
  simp only [zero_add, smoothLiftWord_length]
  exact hq.of_le (by exact_mod_cast Nat.le_of_lt_succ a.1.isLt)

theorem classicalFiniteJet_periodicWeak (l : ℕ) (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (l : ℕ∞) q) (hp : AVenhance.IsZ2Periodic q) :
    HasPeriodicOrderedWeakJet (classicalFiniteJet l q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact GalerkinGenerator.classicalWordDerivative_periodic _ q hp
  · intro a
    exact weak_continuous_memL2On (classicalFiniteJet_continuous l q hq a)
  · intro j w i e
    have hj1 : ContDiff ℝ 1 (classicalWordDerivative (smoothLiftWord j.val w) q) := by
      apply classicalWordDerivative_contDiff_finite _ 1 q
      simp only [smoothLiftWord_length]
      exact hq.of_le (by exact_mod_cast (by omega : 1 + j.val ≤ l))
    have heq1 := (contDiff_const.mul hj1 :
      ContDiff ℝ 1 (fun x => e * classicalWordDerivative (smoothLiftWord j.val w) q x))
    have hweak := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i) heq1
    have hder (x : Vec 2) :
        fderiv ℝ (fun y => e * classicalWordDerivative (smoothLiftWord j.val w) q y) x
          (basisVec i) = e * classicalFiniteJet l q (nextIndex2 j w i) x := by
      rw [fderiv_const_mul (hj1.differentiable (by simp) x)]
      simp [classicalFiniteJet, nextIndex2, nextIndex, smoothLiftWord_snoc,
        classicalWordDerivative, AVenhance.spaceGrad]
    intro φ hφ hc hs
    change (∫ x in Set.univ, classicalFiniteJet l q (lowerIndex2 j w) x * e *
      fderiv ℝ φ x (basisVec i)) =
      -∫ x in Set.univ, classicalFiniteJet l q (nextIndex2 j w i) x * e * φ x
    simpa only [hder, classicalFiniteJet, lowerIndex2, lowerIndex, mul_comm] using hweak φ hφ hc hs

def classicalFiniteHk (l : ℕ) (q : Vec 2 → ℝ) (hq : ContDiff ℝ (l : ℕ∞) q)
    (hp : AVenhance.IsZ2Periodic q) : TorusHkFunction l ℝ :=
  ⟨classicalFiniteJet l q, classicalFiniteJet_periodicWeak l q hq hp⟩

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
open Homogenization AVenhance AVRegularity
namespace AVRegularity.EntryWeakProofs

/-! Joint `C¹` regularity of the offset flows of a real chain: for every fixed anchor `r`, the map
`(u, x) ↦ 𝔛(u, x, r)` of the chain geometry is `C¹`. The base flow is a stream flow (jointly
smooth); each child composes the parent flow with the relative displacement of a shear pulse,
which is `C¹` in `(u, θ)` because the pulse is continuous (fundamental theorem of calculus) and
the shear velocity is smooth. -/

/-- The offset flow of a geometry is jointly `C¹` in `(u, x)` at every fixed anchor. -/
def GeomC1 (g : ChainGeom) : Prop :=
  ∀ r : ℝ, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 p.1 p.2 r)

/-- The shear velocity of a pulse is `C¹`. -/
theorem contDiff_ocShearVel (α q : ℝ) (Λ m : ℕ) (k : ℤ) :
    ContDiff ℝ 1 (ocShearVel α q Λ m k) := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (ocShear α q Λ m k) :=
    AVRegularity.CycleReference.ocShear_contDiff α q Λ m k
  have hc : ContDiff ℝ 1 (fderiv ℝ (ocShear α q Λ m k)) :=
    (hψ.fderiv_right (m := 1) (by simp)).of_le le_rfl
  have hg : ∀ j : Fin 2, ContDiff ℝ 1 (fun y => spaceGrad (ocShear α q Λ m k) y j) := fun j =>
    hc.clm_apply contDiff_const
  change ContDiff ℝ 1 (fun y => sigmaMat.mulVec (spaceGrad (ocShear α q Λ m k) y))
  refine contDiff_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (contDiff_const.mul (hg 0)).add (contDiff_const.mul (hg 1))

/-- The relative displacement is `C¹` in `(u, θ)`. -/
theorem contDiff_relDisp (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (r : ℝ) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 => D.relDisp k pk p.1 r p.2) := by
  have hc : Continuous (ocPulse D.α D.q D.Λ D.ζ k pk) :=
    AVRegularity.CycleReference.ocPulse_continuous hζ pk
  have hF : ContDiff ℝ 1 (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) := by
    rw [contDiff_one_iff_deriv]
    have hd : ∀ u, HasDerivAt (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v)
        (ocPulse D.α D.q D.Λ D.ζ k pk u) u := fun u =>
      intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    refine ⟨fun u => (hd u).differentiableAt, ?_⟩
    have : deriv (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) =
        ocPulse D.α D.q D.Λ D.ζ k pk := funext fun u => (hd u).deriv
    rw [this]; exact hc
  unfold OCData.relDisp
  exact ((hF.comp contDiff_fst).smul
    ((contDiff_ocShearVel _ _ _ _ _).comp (contDiff_snd.const_smul _))).const_smul _

theorem geomC1_childGeom (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) {g : ChainGeom} (hg : GeomC1 g) : GeomC1 (D.childGeom k pk s' c g) := by
  intro r
  have hA : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => g.1 g.2.2 p.2 r) :=
    (hg r).comp (contDiff_const.prodMk contDiff_snd)
  have hR : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => D.relDisp k pk p.1 r
      ((D.eps k)⁻¹ • g.1 g.2.2 p.2 r + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) :=
    (contDiff_relDisp D hζ k pk r).comp
      (contDiff_fst.prodMk ((hA.const_smul _).add contDiff_const))
  exact (hg g.2.2).comp (contDiff_fst.prodMk (hA.add (hR.const_smul _)))

theorem geomC1_geomAux (D : OCData) (hζ : IsFastProfile D.ζ) :
    ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) {g : ChainGeom},
      GeomC1 g → GeomC1 (D.geomAux k sl cs g)
  | [], k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | _ :: _ :: _ => exact hg
  | c :: cs, k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | pk :: pk1 :: rest =>
      exact geomC1_geomAux D hζ cs (k + 1) (pk1 :: rest) (geomC1_childGeom D hζ k pk _ c hg)

/-- **The chain geometry is jointly `C¹`.** -/
theorem geomC1_geom (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    GeomC1 (ch.geom D) := by
  refine geomC1_geomAux D hζ _ _ _ ?_
  intro r
  have h := AVRegularity.CycleReference.streamFlow_joint_smooth (D.hΦ ch.baseLevel)
  exact ((h.of_le (by exact_mod_cast le_top)).comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! A data-independent threshold supplies the primitive transfer shear bound. -/

theorem uniform_weak_transfer_shear_eventually_small (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → ∀ i ≥ M, ∀ slot t,
      ocCutoff D.α D.q D.Λ (i + 1) slot t ≠ 0 →
      |D.slotAnchor (i + 1) slot - t| * ocA D.α D.q D.Λ i ≤ 1 := by
  obtain ⟨M, hM, hb⟩ := weak_anchor_product_eventually_small
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ 1 1 (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ i hi slot t hcut
  have hΛ' : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have ha := ChildInert.anchor_dist D.α D.q hΛ' (i + 1) slot t hcut
  change |t - D.slotAnchor (i + 1) slot| ≤ _ at ha
  have hA : 0 ≤ ocA D.α D.q D.Λ i := Real.rpow_nonneg
    (Construction.Stream.ocEpsilon_pos hΛ').le _
  have hp : ocA D.α D.q D.Λ i * ocTauPP D.α D.q D.Λ (i + 1) ≤ 1 := by
    simpa only [one_mul, Nat.add_sub_cancel, hDα, hDq, hDΛ] using
      hb (i + 1) (by omega)
  calc
    _ ≤ ocTauPP D.α D.q D.Λ (i + 1) * ocA D.α D.q D.Λ i :=
      mul_le_mul_of_nonneg_right (by simpa only [abs_sub_comm] using ha) hA
    _ ≤ 1 := by rw [mul_comm]; exact hp

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

/-! All spatial reserves of an actual offset flow follow by finite composition of smooth shears. -/

def GeomSpatialSmooth (g : ChainGeom) : Prop :=
  ∀ u r : ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun x => g.1 u x r)

theorem ocShearVel_spatial_smooth (α q : ℝ) (Λ m : ℕ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (ocShearVel α q Λ m k) := by
  have hψ := CycleReference.ocShear_contDiff α q Λ m k
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (ocShear α q Λ m k)) :=
    hψ.fderiv_right (by simp)
  have hg : ∀ j : Fin 2, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => spaceGrad (ocShear α q Λ m k) y j) :=
    fun j => hc.clm_apply contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞) (fun y => sigmaMat.mulVec (spaceGrad (ocShear α q Λ m k) y))
  refine contDiff_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (contDiff_const.mul (hg 0)).add (contDiff_const.mul (hg 1))

theorem relDisp_spatial_smooth (D : OCData) (k : ℕ) (pk : ℤ) (u r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (D.relDisp k pk u r) := by
  unfold OCData.relDisp
  exact (((ocShearVel_spatial_smooth _ _ _ _ _).comp
    (contDiff_id.const_smul _)).const_smul _).const_smul _

theorem geomSpatialSmooth_childGeom (D : OCData) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) {g : ChainGeom} (hg : GeomSpatialSmooth g) :
    GeomSpatialSmooth (D.childGeom k pk s' c g) := by
  intro u r
  have hA := hg g.2.2 r
  have hR := (relDisp_spatial_smooth D k pk u r).comp
    ((hA.const_smul ((D.eps k)⁻¹)).add
      (show ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 =>
        c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)) from contDiff_const))
  exact (hg u g.2.2).comp (hA.add (hR.const_smul _))

theorem geomSpatialSmooth_geomAux (D : OCData) :
    ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) {g : ChainGeom},
      GeomSpatialSmooth g → GeomSpatialSmooth (D.geomAux k sl cs g)
  | [], k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | _ :: _ :: _ => exact hg
  | c :: cs, k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | pk :: pk1 :: rest =>
      exact geomSpatialSmooth_geomAux D cs (k + 1) (pk1 :: rest)
        (geomSpatialSmooth_childGeom D k pk _ c hg)

theorem geomSpatialSmooth_geom (D : OCData) (A : RealChain) :
    GeomSpatialSmooth (A.geom D) := by
  refine geomSpatialSmooth_geomAux D _ _ _ ?_
  intro u r
  exact (CycleReference.streamFlow_joint_smooth (D.hΦ A.baseLevel)).comp
    (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Child offset Jacobians factor into the two parent charts and the relative shear. -/

def childShearMap (D : OCData) (k : ℕ) (pk : ℤ) (u r : ℝ)
    (c : ChainChild) (g : ChainGeom) (x : Vec 2) : Vec 2 :=
  x + D.eps k • D.relDisp k pk u r
    ((D.eps k)⁻¹ • x + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))

theorem childShearMap_spatial_smooth (D : OCData) (k : ℕ) (pk : ℤ) (u r : ℝ)
    (c : ChainChild) (g : ChainGeom) :
    ContDiff ℝ (⊤ : ℕ∞) (childShearMap D k pk u r c g) :=
  contDiff_id.add (((relDisp_spatial_smooth D k pk u r).comp
    ((contDiff_id.const_smul _).add contDiff_const)).const_smul _)

theorem childGeom_jacobian_factorization (D : OCData) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) (g : ChainGeom) (hg : GeomSpatialSmooth g) (u r : ℝ) (x : Vec 2) :
    jacMatrix (fun y => (D.childGeom k pk s' c g).1 u y r) x =
      jacMatrix (fun y => g.1 u y g.2.2)
        (childShearMap D k pk u r c g (g.1 g.2.2 x r)) *
        (jacMatrix (childShearMap D k pk u r c g) (g.1 g.2.2 x r) *
          jacMatrix (fun y => g.1 g.2.2 y r) x) := by
  let f := fun y => g.1 u y g.2.2
  let z := childShearMap D k pk u r c g
  let p := fun y => g.1 g.2.2 y r
  have hf : Differentiable ℝ f := (hg u g.2.2).differentiable (by simp)
  have hz : Differentiable ℝ z :=
    (childShearMap_spatial_smooth D k pk u r c g).differentiable (by simp)
  have hp : Differentiable ℝ p := (hg g.2.2 r).differentiable (by simp)
  change jacMatrix (f ∘ (z ∘ p)) x = _
  rw [CycleReference.jacMatrix_comp x (hf _) ((hz.comp hp) _)]
  rw [CycleReference.jacMatrix_comp x (hz _) (hp _)]
  rfl

/-! A literal child step preserves smoothness in every independent center and phase parameter. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_child_geometry_flow_contDiff
    (D : OCData) (k : ℕ) (slot : ℤ) (anchor parentAnchor u r : ℝ)
    (flow : P → ℝ → Vec 2 → ℝ → Vec 2) (center c phase : P → Vec 2)
    (hflow : ∀ u r, ContDiff ℝ (⊤ : ℕ∞) (fun Y : P × Vec 2 => flow Y.1 u Y.2 r))
    (hcenter : ContDiff ℝ (⊤ : ℕ∞) center)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hp : ContDiff ℝ (⊤ : ℕ∞) phase) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : P × Vec 2 =>
      (D.childGeom k slot anchor ⟨c Y.1, phase Y.1⟩
        (flow Y.1, center Y.1, parentAnchor)).1 u Y.2 r) := by
  have hA := hflow parentAnchor r
  have hZ : ContDiff ℝ (⊤ : ℕ∞) (fun Y : P × Vec 2 =>
      (D.eps k)⁻¹ • flow Y.1 parentAnchor Y.2 r +
        (phase Y.1 - (D.eps k)⁻¹ • (center Y.1 + c Y.1))) :=
    (hA.const_smul _).add ((hp.comp contDiff_fst).sub
      (((hcenter.add hc).comp contDiff_fst).const_smul _))
  have hR := (relDisp_spatial_smooth D k slot u r).comp hZ
  exact (hflow u parentAnchor).comp (contDiff_fst.prodMk (hA.add (hR.const_smul _)))

theorem independent_child_geometry_center_contDiff
    (D : OCData) (k : ℕ) (slot : ℤ) (anchor parentAnchor : ℝ)
    (flow : P → ℝ → Vec 2 → ℝ → Vec 2) (center c phase : P → Vec 2)
    (hflow : ContDiff ℝ (⊤ : ℕ∞) (fun Y : P × Vec 2 => flow Y.1 anchor Y.2 parentAnchor))
    (hcenter : ContDiff ℝ (⊤ : ℕ∞) center)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y =>
      (D.childGeom k slot anchor ⟨c Y, phase Y⟩
        (flow Y, center Y, parentAnchor)).2.1) :=
  hflow.comp (contDiff_id.prodMk (hcenter.add hc))
end

/-! Each Jacobian entry jet is bounded by the next full chart derivative. -/

theorem jacobian_entry_derivative_norm_le (F : Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i j : Fin 2) (n : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun y => jacMatrix F y i j) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) F x‖ := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hb := norm_iteratedFDeriv_clm_apply_const
    (c := basisVec j) (hd.contDiffAt (x := x)) (n := n) (by simp)
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun y => (fderiv ℝ F y) (basisVec j)) :=
    hd.clm_apply contDiff_const
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hL : ‖L‖ ≤ 1 := by
    exact L.opNorm_le_bound (by norm_num) (fun z => by
      simpa only [L, ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm z i)
  have hp := L.norm_iteratedFDeriv_comp_left (hv.contDiffAt (x := x)) (n := n) (by simp)
  have hp' : ‖iteratedFDeriv ℝ n (fun y => jacMatrix F y i j) x‖ ≤
      ‖iteratedFDeriv ℝ n (fun y => (fderiv ℝ F y) (basisVec j)) x‖ := by
    change ‖iteratedFDeriv ℝ n (L ∘ fun y => (fderiv ℝ F y) (basisVec j)) x‖ ≤ _
    exact hp.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have hj : ‖(basisVec j : Vec 2)‖ = 1 := by simp [basisVec, Pi.norm_single]
  rw [hj, one_mul, norm_iteratedFDeriv_fderiv] at hb
  exact hp'.trans hb

end AVRegularity.EntryWeakProofs
end
end

section
/-! The classical Fourier lift has the value class of the original Sobolev field. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Heat AVenhance.Infra.Torus
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.Analysis.Convolution

local instance sobolevFourierRepresentativeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sobolevFourierRepresentativeAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sobolevFourierRepresentativeProbTorus : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVRegularity.EntryWeakProofs

theorem realFourierLift_eq_continuous (K : ℕ) (hK : 2 ≤ K) (f : TorusHk K ℝ) (x : Vec 2) :
    realFourierLift K f x = torusFourierContinuous
      (frozenCellToTorusL2 (f.toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 K))) (toUnitTorus 2 x) := by
  have hs := realJetFourier_norm_summable K f (valueIndex2 K) (by exact hK)
  have hcoeff : Summable (fun k : Frequency => ‖UnitAddTorus.mFourierCoeff
      (frozenCellToTorusL2 (f.toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 K))) k‖) := by
    simpa only [realJetFourier, UnitAddTorus.mFourierBasis_repr] using hs
  rw [torusFourierContinuous_eval _ hcoeff x]
  apply tsum_congr
  intro k
  dsimp only [realFourierMode, realJetFourier]
  rw [UnitAddTorus.mFourierBasis_repr]

theorem realClassicalLift_value_ae (K : ℕ) (hK : 2 ≤ K) (f : TorusHk K ℝ) :
    realClassicalLift K f =ᵐ[volume.restrict AVenhance.unitCube] fun x => f.val (valueIndex2 K) x := by
  let u := frozenCellToTorusL2 (f.toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 K))
  have hs : Summable (fun k : Frequency => ‖UnitAddTorus.mFourierCoeff u k‖) := by
    simpa only [u, realJetFourier, UnitAddTorus.mFourierBasis_repr] using
      realJetFourier_norm_summable K f (valueIndex2 K) hK
  have hcu := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (torusFourierContinuous u)
  rw [torusFourierContinuous_toLp u hs] at hcu
  have hur := (memLp_frozenCellTransfer
    (f.toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 K))).coeFn_toLp
  have ht : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin 2))),
      torusFourierContinuous u y = periodicToTorus (fun x => (f.toFunction.jet (valueIndex2 K) x : ℂ)) y := by
    filter_upwards [hcu, hur] with y hy hz
    exact hy.symm.trans hz
  rw [← coupledEnergy_torusMeasure_eq_volume] at ht
  have hc := measurePreserving_torusQuotient_cell.quasiMeasurePreserving.ae ht
  have hm : MeasurableSet AVenhance.unitCube := by
    simpa [AVenhance.unitCube, Set.pi] using
      (MeasurableSet.univ_pi' (fun _ : Fin 2 =>
        (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))))
  filter_upwards [hc, ae_restrict_mem hm, periodicJetRepresentative_ae f.val (valueIndex2 K)]
    with x hx hxc hrep
  have hmem : x ∈ unitCell 2 := by
    intro i
    have hi := hxc i (Set.mem_univ i)
    simpa using (show x i ∈ Set.Ioc (0 : ℝ) 1 from ⟨hi.1, hi.2.le⟩)
  change torusFourierContinuous u (toUnitTorus 2 x) =
    (f.toFunction.jet (valueIndex2 K) (unitTorusRepresentative 2 (toUnitTorus 2 x)) : ℂ) at hx
  rw [unitTorusRepresentative_eq_of_mem_unitCell hmem] at hx
  change (realFourierLift K f x).re = _
  rw [realFourierLift_eq_continuous K hK f x]
  have hh := congrArg Complex.re hx
  simp only [Complex.ofReal_re] at hh
  exact hh.trans hrep

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Actual weak transfer children remain in the same reserved carrier, uniformly in fast phase. -/

theorem uniform_weak_appendChild_eventually_in_carrier (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (bw mres : ℝ) (hbw : 0 < bw) (hmres : -1 < mres) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      ∀ (i j₀ : ℕ) (p slot : ℤ) (A : RealChain), M₀ ≤ i →
      IsCarrierChain D bw j₀ i p mres A → Odd slot → IsScheduledIn D i slot p →
      ∀ t, ocCutoff D.α D.q D.Λ (i + 1) slot t ≠ 0 → ∀ z,
      IsCarrierChain D bw j₀ (i + 1) slot mres (A.appendChild D slot t z) := by
  let bw' := (1 + mres) * bw / 3
  have hres : 0 < 1 + mres := by linarith
  have hbw' : 0 < bw' := by dsimp only [bw']; positivity
  obtain ⟨M₀, hM₀, hp⟩ := weak_anchor_product_eventually_small α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ
    2 (bw' / (64 * (8 * Real.pi ^ 2))) (by positivity)
  refine ⟨M₀, hM₀, ?_⟩
  intro D hDα hDq hDΛ hDζ i j₀ p slot A hi hA hslot hsch t hcut z
  have hΛ' : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hstart : 2 * ocA D.α D.q D.Λ i * ocTauPP D.α D.q D.Λ (i + 1) ≤
      bw' / (64 * (8 * Real.pi ^ 2)) := by
    have hh := hp (i + 1) (by omega)
    simpa only [Nat.add_sub_cancel, hDα, hDq, hDΛ, mul_assoc] using hh
  have hcenter := ChildInert.center_bound D hΛ' hζ' hbw' hstart p slot t hcut z
  have hcenter' : (∑ a : Fin 2, |(D.eps i • D.relDisp i p (D.slotAnchor (i + 1) slot) t z) a|) <
      (1 + mres) * bw / 4 * D.eps i := by
    apply hcenter.trans_eq
    dsimp only [bw']
    ring
  have hctx := hA.1
  have hslotA := hA.2.2.2.1
  unfold RealChain.appendChild
  rw [hctx, hslotA]
  exact weak_carrier_append_child D bw mres j₀ i p slot A hA hslot hsch
    ⟨D.eps i • D.relDisp i p (D.slotAnchor (i + 1) slot) t z,
      z + D.relDisp i p (D.slotAnchor (i + 1) slot) t z⟩ hcenter'

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! The child shear is a translated physical shear multiplied by its pulse integral. -/

theorem pulse_integral_abs_le (D : OCData) (hζ : IsFastProfile D.ζ)
    (k : ℕ) (pk : ℤ) (u r : ℝ) :
    |∫ t in r..u, ocPulse D.α D.q D.Λ D.ζ k pk t| ≤ |u - r| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := r) (b := u) (f := fun t => ocPulse D.α D.q D.Λ D.ζ k pk t) (C := 1)
    (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CycleReference.ocPulse_range hζ pk t).1]
      exact (CycleReference.ocPulse_range hζ pk t).2)
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem childShearMap_physical (D : OCData) (k : ℕ) (hε : 0 < D.eps k)
     (pk : ℤ) (u r : ℝ) (c : ChainChild) (g : ChainGeom) (x : Vec 2) :
    childShearMap D k pk u r c g x = x +
      (∫ t in r..u, ocPulse D.α D.q D.Λ D.ζ k pk t) •
        ocShearVel D.α D.q D.Λ k pk
          (x + D.eps k • (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))) := by
  unfold childShearMap OCData.relDisp
  rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  rw [smul_add, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite child extensions retain joint smoothness while their older geometry stays fixed. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentChainExtensionGeom (D : OCData) : ℕ → ℤ → (P → ChainGeom) →
    List (ℤ × (P → ChainChild)) → P → ChainGeom
  | _, _, g, [] => g
  | level, slot, g, e :: rest =>
      independentChainExtensionGeom D (level + 1) e.1
        (fun Y => D.childGeom level slot (D.slotAnchor (level + 1) e.1) (e.2 Y) (g Y)) rest

theorem independentChainExtensionGeom_joint_smooth (D : OCData)
    (es : List (ℤ × (P → ChainChild)))
    (hs : ∀ e ∈ es, ContDiff ℝ (⊤ : ℕ∞) (fun Y => (e.2 Y).center) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun Y => (e.2 Y).phase))
    (level : ℕ) (slot : ℤ) (g : P → ChainGeom) (anchor : ℝ)
    (ha : ∀ Y, (g Y).2.2 = anchor)
    (hf : ∀ u r, ContDiff ℝ (⊤ : ℕ∞) (fun Y : P × Vec 2 => (g Y.1).1 u Y.2 r))
    (hc : ContDiff ℝ (⊤ : ℕ∞) (fun Y => (g Y).2.1)) :
    (∀ u r, ContDiff ℝ (⊤ : ℕ∞) (fun Y : P × Vec 2 =>
      (independentChainExtensionGeom D level slot g es Y.1).1 u Y.2 r)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun Y =>
      (independentChainExtensionGeom D level slot g es Y).2.1) := by
  induction es generalizing level slot g anchor with
  | nil => exact ⟨hf, hc⟩
  | cons e rest ih =>
    have he := hs e (List.mem_cons_self)
    let g' := fun Y => D.childGeom level slot (D.slotAnchor (level + 1) e.1) (e.2 Y) (g Y)
    have hg (Y : P) : g Y = ((g Y).1, (g Y).2.1, anchor) := by
      rw [← ha Y]
    have hflow : ∀ u r, ContDiff ℝ (⊤ : ℕ∞) (fun Y : P × Vec 2 => (g' Y.1).1 u Y.2 r) := by
      intro u r
      have heq : (fun Y : P × Vec 2 => (g' Y.1).1 u Y.2 r) =
          (fun Y : P × Vec 2 => (D.childGeom level slot (D.slotAnchor (level + 1) e.1)
            ⟨(e.2 Y.1).center, (e.2 Y.1).phase⟩ ((g Y.1).1, (g Y.1).2.1, anchor)).1 u Y.2 r) := by
        funext Y
        conv_lhs =>
          dsimp only [g']
          rw [hg Y.1]
      rw [heq]
      exact independent_child_geometry_flow_contDiff D level slot (D.slotAnchor (level + 1) e.1) anchor u r
        (fun Y => (g Y).1) (fun Y => (g Y).2.1) (fun Y => (e.2 Y).center)
        (fun Y => (e.2 Y).phase) hf hc he.1 he.2
    have hcenter : ContDiff ℝ (⊤ : ℕ∞) (fun Y => (g' Y).2.1) := by
      have heq : (fun Y => (g' Y).2.1) =
          (fun Y => (D.childGeom level slot (D.slotAnchor (level + 1) e.1)
            ⟨(e.2 Y).center, (e.2 Y).phase⟩ ((g Y).1, (g Y).2.1, anchor)).2.1) := by
        funext Y
        conv_lhs =>
          dsimp only [g']
          rw [hg Y]
      rw [heq]
      exact independent_child_geometry_center_contDiff D level slot (D.slotAnchor (level + 1) e.1) anchor
        (fun Y => (g Y).1) (fun Y => (g Y).2.1) (fun Y => (e.2 Y).center)
        (fun Y => (e.2 Y).phase) (hf (D.slotAnchor (level + 1) e.1) anchor) hc he.1
    exact ih (fun e he => hs e (List.mem_cons_of_mem _ he)) (level + 1) e.1 g'
      (D.slotAnchor (level + 1) e.1) (fun _ => rfl) hflow hcenter

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Finite genuine joint source data, with canonical slow-jet reserves produced from the original source. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

structure JointSourceReserve (H : ℕ) (f : ℝ → Vec 2 → Vec 2 → E) where
  regular : ∀ t, ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × Vec 2 => f t X.1 X.2)
  periodic : ∀ t Y, AVenhance.IsZ2Periodic (fun z => f t z Y)
  measurable : ∀ Y, Measurable (fun a : ℝ × Vec 2 => f a.1 a.2 Y)
  budget : ℕ → ℝ
  budget_nonneg : ∀ n, 0 ≤ budget n
  derivative_bound : ∀ n, n ≤ H → ∀ t X,
    ‖iteratedFDeriv ℝ n (fun X : Vec 2 × Vec 2 => f t X.1 X.2) X‖ ≤ budget n

def sourceSlowJetFamily (f : ℝ → Vec 2 → Vec 2 → E) (p : ℕ × ℕ) :
    ℝ → Vec 2 → Vec 2 → E := fun t z Y => sourceParameterJet f p Y t z

def JointSourceReserve.slowJet {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (p : ℕ × ℕ) (R : ℕ) (hR : p.1 + p.2 + R ≤ H) :
    JointSourceReserve R (sourceSlowJetFamily f p) where
  regular := sourceParameterJet_joint_contDiff f p R
    (fun t => (Q.regular t).of_le (by exact_mod_cast hR))
  periodic := fun t Y => sourceParameterJet_periodic f Q.periodic p Y t
  measurable := fun Y => finite_sourceParameterJet_measurable f p
    (fun t z => ((Q.regular t).of_le
      (by exact_mod_cast (show p.1 + p.2 ≤ H by omega))).comp₂ contDiff_const contDiff_id)
    Q.measurable Y
  budget := fun n => Q.budget (p.1 + p.2 + n)
  budget_nonneg := fun n => Q.budget_nonneg _
  derivative_bound := fun n hn t X => (sourceParameterJet_joint_derivative_bound f p n
    (fun t => (Q.regular t).of_le
      (by exact_mod_cast (show p.1 + p.2 + n ≤ H by omega))) t X).trans
    (Q.derivative_bound _ (by omega) t X)

omit [BorelSpace E] [SecondCountableTopology E] in
theorem JointSourceReserve.fast_contDiff {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (t : ℝ) (Y : Vec 2) :
    ContDiff ℝ (H : ℕ∞) (fun z => f t z Y) :=
  (Q.regular t).comp₂ contDiff_id contDiff_const

omit [BorelSpace E] [SecondCountableTopology E] in
theorem JointSourceReserve.fast_derivative_bound {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (n : ℕ) (hn : n ≤ H) (t : ℝ) (Y z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun x => f t x Y) z‖ ≤ Q.budget n := by
  rw [jointFastDerivative_eq n _ ((Q.regular t).of_le (by exact_mod_cast hn)) z Y]
  have hb := (jointFastRestrictionCLM (E := E) n).le_opNorm
    (iteratedFDeriv ℝ n (fun X : Vec 2 × Vec 2 => f t X.1 X.2) (z, Y))
  exact hb.trans (((mul_le_mul_of_nonneg_right (jointFastRestrictionCLM_norm_le_one n)
    (norm_nonneg _)).trans_eq (one_mul _)).trans (Q.derivative_bound n hn t (z, Y)))

local instance jointSourceReserveFiniteCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simp only [Measure.restrict_apply_univ, weak_unitCube_volume]; exact ENNReal.one_lt_top⟩

omit [BorelSpace E] in
theorem JointSourceReserve.slice_memLp {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (t : ℝ) (Y : Vec 2) :
    MemLp (fun z => f t z Y) 2 (volume.restrict AVenhance.unitCube) := by
  apply MemLp.of_bound (Q.fast_contDiff t Y).continuous.aestronglyMeasurable (Q.budget 0)
  exact Filter.Eventually.of_forall fun z => by
    simpa only [norm_iteratedFDeriv_zero] using Q.fast_derivative_bound 0 (Nat.zero_le H) t Y z

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

/-! Entrywise jet estimates control the matrix jet in the supremum norm. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem matrix_derivative_norm_le_of_entries
    (A : P → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (n : ℕ) (x : P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i j, ‖iteratedFDeriv ℝ n (fun y => A y i j) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n A x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro w
  have hprod : 0 ≤ C * ∏ k, ‖w k‖ := mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hprod).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hprod).mpr
  intro j
  let L : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 2 → Vec 2) →L[ℝ] Vec 2)
  have he := L.iteratedFDeriv_comp_left (hA.contDiffAt (x := x)) (i := n) (by simp)
  have hev := congrArg (fun F => F w) he
  change iteratedFDeriv ℝ n (fun y => A y i j) x w =
    (iteratedFDeriv ℝ n A x w) i j at hev
  rw [← hev]
  exact (ContinuousMultilinearMap.le_opNorm _ w).trans
    (mul_le_mul_of_nonneg_right (hb i j) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
open AVRegularity.CycleReference
namespace AVRegularity.EntryWeakProofs

/-! The physical shear operator bound. -/

theorem scaled_shear_derivative_norm_le {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    (k : ℤ) (hk : Odd k) (c : ℝ) (b : ℕ) (y : Vec 2) :
    ‖iteratedFDeriv ℝ b (fun x => c • ocShearVel α q Λ m k x) y‖ ≤
      (|c| *
        (2 * Real.pi * ocEpsilon q Λ m ^ α) *
          (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ b) := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  let A := 2 * Real.pi * ocEpsilon q Λ m ^ α
  let ω := 2 * Real.pi * (ocEpsilon q Λ m)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hamp : 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ = A := by
    dsimp [A]
    rw [mul_assoc, ← div_eq_mul_inv, ← Real.rpow_sub_one he.ne']
    congr 2
    ring
  have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
    rcases hk with ⟨l, hl⟩
    have hn := Int.emod_nonneg k (b := 4) (by norm_num)
    have hu := Int.emod_lt k (b := 4) (by norm_num)
    omega
  rcases hmod with h1 | h3
  · have hf : (fun x => c • ocShearVel α q Λ m k x) =
        fun x : Vec 2 => (c * A * Real.cos (ω * x 0)) • basisVec 1 := by
      funext x
      rw [ocShearVel_horizontal h1 x, hamp]
      ext i
      fin_cases i <;> simp [basisVec, ω, smul_eq_mul, mul_assoc]
    rw [hf]
    have hb := cosine_vector_derivative_norm_le (c * A) ω hω.le 0 1 b y
    rw [abs_mul, abs_of_pos hA] at hb
    exact hb
  · have hf : (fun x => c • ocShearVel α q Λ m k x) =
        fun x : Vec 2 => (-c * A * Real.cos (ω * x 1)) • basisVec 0 := by
      funext x
      rw [ocShearVel_vertical h3 x, hamp]
      ext i
      fin_cases i <;> simp [basisVec, ω, smul_eq_mul, mul_assoc]
    rw [hf]
    have hb := cosine_vector_derivative_norm_le (-c * A) ω hω.le 1 0 b y
    rw [abs_mul, abs_neg, abs_of_pos hA] at hb
    exact hb

theorem physical_shear_fderiv_norm_le {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    (k : ℤ) (hk : Odd k) (y : Vec 2) :
    ‖fderiv ℝ (ocShearVel α q Λ m k) y‖ ≤
      (4 * Real.pi ^ 2) * ocA α q Λ m := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have h := scaled_shear_derivative_norm_le (α := α) (q := q) (m := m) hΛ k hk 1 1 y
  simp only [one_smul, norm_iteratedFDeriv_one, abs_one, one_mul, pow_one] at h
  have hp : ocEpsilon q Λ m ^ α * (ocEpsilon q Λ m)⁻¹ = ocA α q Λ m := by
    rw [← div_eq_mul_inv, ← Real.rpow_sub_one he.ne']
    unfold ocA
    congr 1
    ring
  have hc : (2 * Real.pi * ocEpsilon q Λ m ^ α) *
      (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) = (4 * Real.pi ^ 2) * ocA α q Λ m := by
    calc
      _ = (4 * Real.pi ^ 2) * (ocEpsilon q Λ m ^ α * (ocEpsilon q Λ m)⁻¹) := by ring
      _ = _ := by rw [hp]
  exact h.trans_eq hc

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! A slow cutoff extends carrier-local forcing smoothly to the full parameter space. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cutoffSource (χ : Vec 2 → ℝ) (f : ℝ → Vec 2 → Vec 2 → E)
    (t : ℝ) (z Y : Vec 2) : E := χ Y • f t z Y

theorem cutoffSource_eventually_zero (χ : Vec 2 → ℝ) (f : ℝ → Vec 2 → Vec 2 → E)
    (t : ℝ) (X : Vec 2 × Vec 2) (hX : X.2 ∉ tsupport χ) :
    (fun Z : Vec 2 × Vec 2 => cutoffSource χ f t Z.1 Z.2) =ᶠ[𝓝 X] 0 := by
  have hχ : χ =ᶠ[𝓝 X.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hX
  have hh := (continuous_snd.tendsto X).eventually hχ
  filter_upwards [hh] with Z hZ
  simp only [cutoffSource, hZ, Pi.zero_apply, zero_smul]

theorem cutoffSource_joint_contDiff (H : ℕ) (U : Set (Vec 2)) (hU : IsOpen U)
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ (H : ℕ∞) χ) (hs : tsupport χ ⊆ U)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t, ContDiffOn ℝ (H : ℕ∞) (fun X : Vec 2 × Vec 2 => f t X.1 X.2)
      {X | X.2 ∈ U}) (t : ℝ) :
    ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × Vec 2 => cutoffSource χ f t X.1 X.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro X
  by_cases hX : X.2 ∈ U
  · exact ((hχ.comp contDiff_snd).contDiffAt).smul
      ((hf t X hX).contDiffAt ((hU.preimage continuous_snd).mem_nhds hX))
  · have hn : X.2 ∉ tsupport χ := fun hh => hX (hs hh)
    exact (contDiff_const : ContDiff ℝ (H : ℕ∞) (fun _ : Vec 2 × Vec 2 => (0 : E))).contDiffAt
      |>.congr_of_eventuallyEq (cutoffSource_eventually_zero χ f t X hn)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The independent child family shares one slot anchor at each fixed discrete stage. -/

section
variable {P : Type*}

def independentChainExtensionAnchor (D : OCData) : ℕ → ℝ → List (ℤ × (P → ChainChild)) → ℝ
  | _, anchor, [] => anchor
  | level, _, e :: rest =>
      independentChainExtensionAnchor D (level + 1) (D.slotAnchor (level + 1) e.1) rest

theorem independentChainExtensionGeom_anchor (D : OCData) (es : List (ℤ × (P → ChainChild)))
    (level : ℕ) (slot : ℤ) (g : P → ChainGeom) (anchor : ℝ) (ha : ∀ Y, (g Y).2.2 = anchor)
    (Y : P) :
    (independentChainExtensionGeom D level slot g es Y).2.2 =
      independentChainExtensionAnchor D level anchor es := by
  induction es generalizing level slot g anchor with
  | nil => exact ha Y
  | cons e rest ih =>
    exact ih (level + 1) e.1
      (fun Z => D.childGeom level slot (D.slotAnchor (level + 1) e.1) (e.2 Z) (g Z))
      (D.slotAnchor (level + 1) e.1) (fun _ => rfl)
end

/-! Literal forcing identities preserve every numeric entry of the source reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def JointSourceReserve.congrSource {H : ℕ} {f g : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (he : f = g) : JointSourceReserve H g := he ▸ Q

omit [BorelSpace E] [SecondCountableTopology E] in
theorem JointSourceReserve.congrSource_budget {H : ℕ} {f g : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (he : f = g) (n : ℕ) :
    (Q.congrSource he).budget n = Q.budget n := by
  subst g
  rfl
end

end AVRegularity.EntryWeakProofs
end
end
