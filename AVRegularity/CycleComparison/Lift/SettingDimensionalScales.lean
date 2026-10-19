-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.TimeIntegration
import AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
public import AVRegularity.CycleComparison.Lift.LeftTerm
import AVRegularity.CycleComparison.Residual.Jets.Lift
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Differentiating a finite flux expansion gives the literal divergence-form action. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem meanApply_of_flux_coefficients (n : ℕ) (hn : 2 ≤ n)
    (c : Fin 2 → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2)
    (hzero : ∀ k (α : DerivativeWord2 0) Y v u, c k 0 α t Y 0 v u = 0)
    (hreg : ∀ m ≤ n - 1, ∀ (α : DerivativeWord2 m) k,
      Differentiable ℝ (fun Y v => ∑ u, c k m α t Y 0 v u (orderedDerivative α (f t) Y u))) :
    (∑ k : Fin 2, fderiv ℝ (fun Y => liftApply (n - 1) (c k) f t Y 0) X (basisVec k)) =
      meanApply n (fun d α t Y k => c k (d - 1) α t Y 0) f t X := by
  classical
  let F := fun (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) Y v =>
    ∑ u, c k m α t Y 0 v u (orderedDerivative α (f t) Y u)
  have he (k : Fin 2) : (fun Y => liftApply (n - 1) (c k) f t Y 0) =
      fun Y => ∑ d ∈ Finset.Icc 2 n, ∑ α : DerivativeWord2 (d - 1), F k (d - 1) α Y := by
    funext Y
    have hz : (∑ α : DerivativeWord2 0, F k 0 α Y) = 0 := by
      ext v
      simp only [F, Finset.sum_apply, hzero, zero_apply, Finset.sum_const_zero, Pi.zero_apply]
    have hs := sum_range_zero_order_shift n (by omega)
      (fun m => ∑ α : DerivativeWord2 m, F k m α Y) hz
    have hn' : n - 1 + 1 = n := by omega
    ext v
    simpa only [liftApply, hn', F, Finset.sum_apply] using congrFun hs v
  simp_rw [he]
  have hd (k : Fin 2) :
      fderiv ℝ (fun Y => ∑ d ∈ Finset.Icc 2 n, ∑ α : DerivativeWord2 (d - 1), F k (d - 1) α Y) X =
        ∑ d ∈ Finset.Icc 2 n, ∑ α : DerivativeWord2 (d - 1), fderiv ℝ (F k (d - 1) α) X := by
    rw [fderiv_fun_sum]
    · apply Finset.sum_congr rfl
      intro d hd
      exact fderiv_fun_sum (fun α _ => hreg (d - 1) (by have h := Finset.mem_Icc.mp hd; omega) α k X)
    · intro d hd
      exact DifferentiableAt.fun_sum (fun α _ =>
        hreg (d - 1) (by have h := Finset.mem_Icc.mp hd; omega) α k X)
  simp only [hd, sum_apply]
  ext v
  simp only [Finset.sum_apply, meanApply, F]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
end

/-! The explicit first-order metric coefficient array acts as the molecular metric flux. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem metricFluxCoefficient_apply (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) :
    liftApply 1 (metricFluxCoefficient η G k) f t X z =
      -η • ∑ j : Fin 2, G t X k j • fderiv ℝ (f t) X (basisVec j) := by
  have he : (∑ α : DerivativeWord2 1, G t X k (α 0) •
      fderiv ℝ (f t) X (basisVec (α 0))) =
      ∑ j : Fin 2, G t X k j • fderiv ℝ (f t) X (basisVec j) := by
    have hs := Equiv.sum_comp firstWordEquiv.symm
      (fun α : DerivativeWord2 1 => G t X k (α 0) • fderiv ℝ (f t) X (basisVec (α 0)))
    simpa only [firstWordEquiv, Equiv.coe_fn_symm_mk] using hs.symm
  ext v
  simp only [liftApply, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    metricFluxCoefficient_zero, zero_apply, Finset.sum_const_zero,
    metricFluxCoefficient_one, smul_apply, blockIdentityEntry_apply, orderedDerivative_first_word]
  have hu (α : DerivativeWord2 1) :
      (∑ u, (-η * G t X k (α 0)) • Pi.single u (fderiv ℝ (f t) X (basisVec (α 0)) u) v) =
      (-η * G t X k (α 0)) • fderiv ℝ (f t) X (basisVec (α 0)) v := by
    rw [Finset.sum_eq_single v]
    · rw [Pi.single_eq_same]
    · intro u hu huv
      rw [Pi.single_eq_of_ne (Ne.symm huv), smul_zero]
    · simp
  simp only [hu]
  have hs := congrFun (congrArg (fun a => -η • a) he) v
  simpa only [Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply] using hs
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The common induction state records actual rectangular jets, transverse geometry, and clamped time measurability. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

structure AmbientLiftCoefficientData (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (n p q : ℕ) (c : LiftCoeff ι h) (M : ι → ι → ℝ) : Prop where
  nonneg : ∀ v u, 0 ≤ M v u
  box : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Set.Icc a b,
    IsBoxSmooth p q (fun X z => c m α t X z v u)
  bound : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, ∀ r ≤ p, ∀ s ≤ q,
    ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y => c m α t Y y v u) z) X‖ ≤
        M v u * lam ^ (n - m + r)
  transverse : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
    IsTransverseOn par (Set.Icc a b) (fun t X z => c m α t X z v u)
  measurable : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, ∀ l : (h u →L[ℝ] h v) →L[ℝ] ℝ,
    ∀ X z, Measurable (fun t => l (c m α (Set.projIcc a b hab t) X z v u))

theorem AmbientLiftCoefficientData.mono {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
    {n p q p' q' : ℕ} {c : LiftCoeff ι h} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (hp : p' ≤ p) (hq : q' ≤ q) : AmbientLiftCoefficientData par a b hab lam n p' q' c M := by
  refine ⟨data.nonneg, ?_, ?_, data.transverse, data.measurable⟩
  · intro m hm α v u t ht
    exact (data.box m hm α v u t ht).mono hp hq
  · intro m hm α v u r hr s hs t ht X z
    exact data.bound m hm α v u r (hr.trans hp) s (hs.trans hq) t ht X z

theorem AmbientLiftCoefficientData.enlarge {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
    {n p q : ℕ} {c : LiftCoeff ι h} {M M' : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M) (hlam : 0 ≤ lam)
    (hM' : ∀ v u, M v u ≤ M' v u) : AmbientLiftCoefficientData par a b hab lam n p q c M' := by
  refine ⟨fun v u => (data.nonneg v u).trans (hM' v u), data.box, ?_, data.transverse, data.measurable⟩
  intro m hm α v u r hr s hs t ht X z
  exact (data.bound m hm α v u r hr s hs t ht X z).trans
    (mul_le_mul_of_nonneg_right (hM' v u) (pow_nonneg hlam _))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CycleComparison.Lift

/-! The smooth-test weak-jet construction, adapted to finite C¹ vector-valued cell fields. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def classicalCellJet (f : Vec 2 → E) : RawJet2 1 E :=
  fun a x => if h : 0 < a.1.val then fderiv ℝ f x (basisVec (a.2 ⟨0, h⟩)) else f x

omit [InnerProductSpace ℝ E] in
theorem continuous_cell_memLp (f : Vec 2 → E) (hf : Continuous f) :
    MemLp f 2 (volume.restrict AVenhance.unitCube) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).mpr
  exact (hf.norm.pow 2).continuousOn.integrableOn_compact
    WeakAlgebra.weakSpatialClosedCell_compact |>.mono_set WeakAlgebra.weakUnitCube_subset_closedCell

theorem classicalCellJet_continuous (f : Vec 2 → E) (hf : ContDiff ℝ 1 f) (a : JetIndex2 1) :
    Continuous (classicalCellJet f a) := by
  by_cases ha : 0 < a.1.val
  · have he : classicalCellJet f a = fun x => fderiv ℝ f x (basisVec (a.2 ⟨0, ha⟩)) := by
      funext x
      simp [classicalCellJet, ha]
    rw [he]
    exact
      ((hf.fderiv_right (m := 0) (by norm_num)).clm_apply
        (contDiff_const : ContDiff ℝ 0 (fun _ : Vec 2 => basisVec (a.2 ⟨0, ha⟩)))).continuous
  · have he : classicalCellJet f a = f := by funext x; simp [classicalCellJet, ha]
    rw [he]
    exact hf.continuous

theorem classicalCellJet_periodic (f : Vec 2 → E) (hf : ContDiff ℝ 1 f)
    (hp : AVenhance.IsZ2Periodic f) (a : JetIndex2 1) :
    AVenhance.IsZ2Periodic (classicalCellJet f a) := by
  by_cases ha : 0 < a.1.val
  · have hd := fderiv_isZ2Periodic (hf.differentiable (by norm_num)) hp
    intro n x
    simp only [classicalCellJet, dite_eq_left ha]
    exact congrArg (fun A => A (basisVec (a.2 ⟨0, ha⟩))) (hd n x)
  · have he : classicalCellJet f a = f := by funext x; simp [classicalCellJet, ha]
    rw [he]
    exact hp

theorem classicalCellJet_periodicWeak (f : Vec 2 → E) (hf : ContDiff ℝ 1 f)
    (hp : AVenhance.IsZ2Periodic f) : HasPeriodicOrderedWeakJet (classicalCellJet f) := by
  refine ⟨classicalCellJet_periodic f hf hp,
    (fun a => continuous_cell_memLp _ (classicalCellJet_continuous f hf a)), ?_⟩
  intro j w i e
  fin_cases j
  have hw : w = Fin.elim0 := Subsingleton.elim _ _
  subst w
  have hs : ContDiff ℝ 1 (fun x => inner ℝ e (f x)) :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : Vec 2 => e)).inner ℝ hf
  have hh := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i) hs
  have he (x : Vec 2) : fderiv ℝ (fun y => inner ℝ e (f y)) x (basisVec i) =
      inner ℝ e (fderiv ℝ f x (basisVec i)) := by
    rw [fderiv_inner_apply ℝ (differentiableAt_const e) (hf.differentiable (by norm_num) x)]
    simp
  simpa [classicalCellJet, lowerIndex2, lowerIndex, nextIndex2, nextIndex, he] using! hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal lift action is a finite list of left terms on the coefficient vector. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def liftComponentLeftTerms (n : ℕ) (c : LiftCoeff ι h) (t : ℝ) (v : ι) :
    List (LeftTerm (∀ i, h i) (h v)) :=
  (Finset.range (n + 1)).toList.flatMap fun m =>
    (Finset.univ.toList : List (DerivativeWord2 m)).flatMap fun α =>
      (Finset.univ.toList : List ι).map fun u =>
        ⟨m, α, fun X z => (c m α t X z v u).comp (ContinuousLinearMap.proj u)⟩

theorem liftComponentLeftTerms_order (n : ℕ) (c : LiftCoeff ι h) (t : ℝ) (v : ι)
    (d : LeftTerm (∀ i, h i) (h v)) (hd : d ∈ liftComponentLeftTerms n c t v) :
    d.order ≤ n := by
  obtain ⟨m, hm, α, hα, u, hu, rfl⟩ := by
    simpa only [liftComponentLeftTerms, List.mem_flatMap, List.mem_map] using hd
  have hm' := Finset.mem_range.mp (Finset.mem_toList.mp hm)
  change m ≤ n
  omega

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Two fixed coordinate evaluations bound the last argument of a full fast jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clm_norm_le_sum_coordinate_values (L : Vec 2 →L[ℝ] E) :
    ‖L‖ ≤ ∑ k : Fin 2, ‖L (basisVec k)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have he : L v = ∑ k : Fin 2, v k • L (basisVec k) := by
    conv_lhs => rw [vec2_eq_sum_basisVec v]
    simp only [map_sum, map_smul]
  rw [he]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul, Real.norm_eq_abs]
  have hv : |v k| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v k
  calc |v k| * ‖L (basisVec k)‖ ≤ ‖v‖ * ‖L (basisVec k)‖ :=
        mul_le_mul_of_nonneg_right hv (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem multilinear_norm_le_sum_last_coordinates (q : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => Vec 2) E) :
    ‖f‖ ≤ ∑ k : Fin 2, ‖jetApply q (basisVec k) f‖ := by
  have hc : ‖(continuousMultilinearCurryRightEquiv' ℝ q (Vec 2) E) f‖ = ‖f‖ :=
    (continuousMultilinearCurryRightEquiv' ℝ q (Vec 2) E).norm_map f
  rw [← hc]
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  apply (clm_norm_le_sum_coordinate_values
    ((continuousMultilinearCurryRightEquiv' ℝ q (Vec 2) E) f v)).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  change ‖jetApply q (basisVec k) f v‖ ≤ ‖jetApply q (basisVec k) f‖ * ∏ i, ‖v i‖
  exact (jetApply q (basisVec k) f).le_opNorm v
end

/-! Full mixed fast jets are reconstructed from two coordinate partials with no dimension factor. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_fast_jet_le_sum_partials {r q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r (q + 1) f) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (q + 1) (f Y) z) X‖ ≤
      ∑ k : Fin 2, ‖iteratedFDeriv ℝ r
        (fun Y => iteratedFDeriv ℝ q (fastPartial k f Y) z) X‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  apply (multilinear_norm_le_sum_last_coordinates q
    (iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (q + 1) (f Y) z) X v)).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  let A := jetApply (F := E) q (basisVec k)
  have he : (fun Y => iteratedFDeriv ℝ q (fastPartial k f Y) z) =
      A ∘ (fun Y => iteratedFDeriv ℝ (q + 1) (f Y) z) := by
    funext Y
    exact iteratedFDeriv_fderiv_apply (hf.1 Y).contDiffAt (basisVec k)
  have hh := ContinuousLinearMap.iteratedFDeriv_comp_left
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E)
    A (hf.2.1 (q + 1) le_rfl z).contDiffAt (x := X) (i := r) le_rfl
  have heval : jetApply q (basisVec k)
      (iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (q + 1) (f Y) z) X v) =
      iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fastPartial k f Y) z) X v := by
    rw [he, hh]
    rfl
  rw [heval]
  exact (iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fastPartial k f Y) z) X).le_opNorm v
end

/-! The prescribed one-periodic scalar shear induces a lattice-periodic cell drift. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_drift_periodic (t : ℝ) (ht : t ∈ Set.Icc a b) :
    AVenhance.IsZ2Periodic (Q.v t) := by
  intro n z
  rw [P.v_shear, P.v_shear]
  have hp := ((P.V_per t ht).int_mul (n par.rev)) (z par.rev)
  have he : V t (z par.rev + (n par.rev : ℝ)) = V t (z par.rev) := by
    simpa only [mul_one] using hp
  change V t (z par.rev + (n par.rev : ℝ)) • basisVec par =
    V t (z par.rev) • basisVec par
  rw [he]
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The scalar shear profile inherits pointwise time measurability from the prescribed drift. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_shear_profile_measurable (x : ℝ) : Measurable (fun t => V t x) := by
  have hm := (continuous_apply par).measurable.comp (P.v_meas (x • basisVec par.rev))
  have he : (fun t => Q.v t (x • basisVec par.rev) par) = fun t => V t x := by
    funext t
    simp [P.v_shear, basisVec_apply]
  change Measurable (fun t => Q.v t (x • basisVec par.rev) par) at hm
  rwa [he] at hm

include P in
theorem setting_transverse_drift_zero (t : ℝ) (z : Vec 2) : Q.v t z par.rev = 0 := by
  rw [P.v_shear t z]
  have hne : par.rev ≠ par := by
    have hh : ∀ p : Fin 2, p.rev ≠ p := by decide
    exact hh par
  simp [basisVec_apply, hne]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleComparison.Lift

/-! Classical jets of a scalar transverse profile inherit joint time-space continuity from its first two profiles. -/

theorem classicalProfileJet_joint_continuousOn (I : Set ℝ) (c : ℝ → ℝ → ℂ)
    (p : Fin 2) (hf : ∀ t ∈ I, Differentiable ℝ (c t))
    (hc : ContinuousOn (Function.uncurry c) (I ×ˢ (Set.univ : Set ℝ)))
    (hd : ContinuousOn (fun x : ℝ × ℝ => deriv (c x.1) x.2)
      (I ×ˢ (Set.univ : Set ℝ))) (a : JetIndex2 1) :
    ContinuousOn (fun x : ℝ × Vec 2 => classicalCellJet (fun z => c x.1 (z p)) a x.2)
      (I ×ˢ (Set.univ : Set (Vec 2))) := by
  have hmap : Continuous (fun x : ℝ × Vec 2 => (x.1, x.2 p)) :=
    continuous_fst.prodMk ((continuous_apply p).comp continuous_snd)
  have hmaps : MapsTo (fun x : ℝ × Vec 2 => (x.1, x.2 p))
      (I ×ˢ (Set.univ : Set (Vec 2))) (I ×ˢ (Set.univ : Set ℝ)) :=
    fun _ hx => ⟨hx.1, mem_univ _⟩
  by_cases ha : 0 < a.1.val
  · let j := a.2 ⟨0, ha⟩
    by_cases hj : j = p
    · apply (hd.comp hmap.continuousOn hmaps).congr
      intro x hx
      simp only [classicalCellJet, dite_eq_left ha]
      rw [fderiv_profile_basis _ (hf x.1 hx.1)]
      exact ite_eq_left hj
    · apply continuousOn_const.congr
      intro x hx
      simp only [classicalCellJet, dite_eq_left ha]
      rw [fderiv_profile_basis _ (hf x.1 hx.1)]
      exact ite_eq_right hj
  · apply (hc.comp hmap.continuousOn hmaps).congr
    intro x _
    simp only [classicalCellJet, dite_eq_right ha]
    rfl

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The setting's physical scales give positive time dilation and the exact dimensional multiplier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem setting_length_pos : 0 < ℓ := by
  rw [P.ℓ_eq]
  exact div_pos P.e_pos (Real.sqrt_pos.2 P.ν_pos)

include P in
theorem setting_dstar_pos : 0 < dstar := by
  rw [P.dstar_eq]
  exact mul_pos (setting_length_pos P) (Real.sqrt_pos.2 P.B_pos)

include P in
theorem setting_dstar_sq : dstar ^ 2 = ℓ ^ 2 * B := by
  rw [P.dstar_eq, mul_pow, Real.sq_sqrt P.B_pos.le]

include P in
theorem setting_physical_time_mem (t : ℝ) (ht : t ∈ Set.Icc (ℓ ^ 2 * a) (ℓ ^ 2 * b)) :
    t / ℓ ^ 2 ∈ Set.Icc a b := by
  have hℓ : 0 < ℓ ^ 2 := pow_pos (setting_length_pos P) 2
  exact ⟨(le_div_iff₀ hℓ).2 (by simpa only [mul_comm] using ht.1),
    (div_le_iff₀ hℓ).2 (by simpa only [mul_comm] using ht.2)⟩

include P in
theorem setting_dimensional_scale_identity (n d r : ℕ) (hn : 2 ≤ n) (hd : d ≤ n) :
    E ^ r * ((ℓ ^ 2)⁻¹ * εc ^ n * ρ ^ d) * (ρ⁻¹) ^ r *
      lam ^ (n - d + r) = B * dstar ^ (n - 2) * (E ^ d / E ^ n) := by
  rw [P.εc_eq, P.lam_eq]
  exact dimensional_scale_identity ℓ B dstar ρ E (ne_of_gt (setting_length_pos P))
    (ne_of_gt (setting_dstar_pos P)) (ne_of_gt P.ρ_pos) (ne_of_gt P.E_pos)
    (setting_dstar_sq P) n d r hn hd

end AVRegularity.CycleComparison.Lift
end
