-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.PriceLedgerC2
import AVRegularity.CycleJoint.Assembly.FollowingExplicitEnergyError
public import AVRegularity.CycleJoint.Assembly.PatchModelBound

section
/-! **The weighted error of one patch**.

For the recentred premises of one patch, the model `P f = trunc_{max Mout K} (ret_Mb (realize Mc f))`
(the seam's cell model, realized and returned at `t_p`). The error of a plane solution `U` from the
localized datum, `U(t_p) - trunc_K P f`, is
- unweighted: `[u(t_p) - ret (Σ uF)] + ret (Σ uF - trunc realize)` (the error of the two-block theorem and the return of
  the seam's masked error), at most `2 (e₂ + c₀ CNp²) S_r`;
- with moment `n'`: `u'(t_p) - trunc_K P f`, where `u'(t_p)` is the return of the following-chart
  curve and the model is bounded by the model bound, at most `2 (c' m₁ + C_M) S_r`;
- weighted with moment `n`: by interpolation, at most `ε² S_old` when
  `(ε₁²)^{1-θ} C₂^θ ≤ ε²`, `θ = n/n'`, after the radius conversion `S_r ≤ Lr^{2 Kmax} S_old`.
Here `S_r = Σ π⁻¹ |loc f|²_r`, `S_old = Σ π⁻¹ |loc f|²_{ρold}`; `u` (two-block) and `u'` are physical
solutions on the whole window and agree with `U` at `t_p`. The prices `e₂` (two-block), `CNp` (the seam)
and `m₁` (the moments) are premises here, discharged by the price ledger.

For an empty index type all sums are `0`. For `n = 0` one has `θ = 0` and the bound is the
unweighted one, and for `K = 0` only values enter. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

attribute [local instance] planeModelTorusNormed planeModelTorusInner planeModelTorusSpace
  planeModelPlaneNormed planeModelPlaneInner planeModelPlaneSpace planeModelTorusPiAdd
  planeModelTorusPiModule planeModelPlanePiAdd planeModelPlanePiModule

section Values

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- The value component is part of every factorial energy. -/
theorem value_norm_sq_le_factorialNormSq {K : ℕ} (ρ : ℝ) (V : PlaneHk Set.univ K E) :
    ‖V.val (valueIndex2 K)‖ ^ 2 ≤ factorialNormSq ρ V.val := by
  unfold factorialNormSq
  have h0 : factorialWeight ρ (0 : Fin (K + 1)).val * derivativeNormSq V.val 0 =
      ‖V.val (valueIndex2 K)‖ ^ 2 := by
    have hw : derivativeNormSq V.val 0 = ‖V.val (valueIndex2 K)‖ ^ 2 :=
      Fintype.sum_eq_single (valueIndex2 K).2 (fun w hw => (hw (funext fun i => i.elim0)).elim)
    have hf : factorialWeight ρ (0 : Fin (K + 1)).val = 1 := by
      simp [factorialWeight]
    rw [hf, hw, one_mul]
  rw [← h0]
  exact Finset.single_le_sum (f := fun j : Fin (K + 1) => factorialWeight ρ j.val *
    derivativeNormSq V.val j) (fun j _ => mul_nonneg (factorialWeight_nonneg _ _)
      (derivativeNormSq_nonneg _ _)) (Finset.mem_univ _)

/-- The slot-`0` localization's `L²` norm is part of every factorial energy of the slot-`K`
localization. -/
theorem loc0_norm_sq_le {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (j : Fin 2 → Fin N) {K : ℕ} (f : TorusHk K E) (ρ : ℝ) :
    ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le K) f)‖ ^ 2 ≤
      factorialNormSq ρ (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) K f).val := by
  rw [spatialPatchLocalizationCLM_truncate_norm_sq, planeHkValueOperator_norm]
  exact value_norm_sq_le_factorialNormSq ρ _

end Values

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The mass-weighted energy of a sum of two families. -/
theorem family_add_energy_le (π : ι → ℝ) (n : ℕ) (ϖ : ℝ) (y : Vec 2) (ρ : ℝ) (K : ι → ℕ)
    (Z X Y : ∀ i, PlaneHk Set.univ (K i) (h i)) (hZ : ∀ i, Z i = X i + Y i) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (X i) ≤
      ENNReal.ofReal a)
    (hY : ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (Y i) ≤
      ENNReal.ofReal b) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (Z i) ≤
      ENNReal.ofReal (2 * (a + b)) := by
  calc ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (Z i)
      ≤ ∑ i, ENNReal.ofReal ((π i)⁻¹) * (2 * (weightedFactorialNormSq n ϖ y ρ (K i) (X i) +
          weightedFactorialNormSq n ϖ y ρ (K i) (Y i))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_right (by
          rw [hZ i]; exact CycleWords.weightedFactorialNormSq_add_le n ϖ y ρ _ _) _
    _ = 2 * (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (X i) +
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (Y i)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 2 * (ENNReal.ofReal a + ENNReal.ofReal b) := mul_le_mul_right (add_le_add hX hY) _
    _ = ENNReal.ofReal (2 * (a + b)) := by
        rw [← ENNReal.ofReal_add ha hb, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- The mass-weighted energy of a difference of two families. -/
theorem family_sub_energy_le (π : ι → ℝ) (n : ℕ) (ϖ : ℝ) (y : Vec 2) (ρ : ℝ) (K : ι → ℕ)
    (X Y : ∀ i, PlaneHk Set.univ (K i) (h i)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (X i) ≤
      ENNReal.ofReal a)
    (hY : ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (Y i) ≤
      ENNReal.ofReal b) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (X i - Y i) ≤
      ENNReal.ofReal (2 * (a + b)) := by
  calc ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (X i - Y i)
      ≤ ∑ i, ENNReal.ofReal ((π i)⁻¹) * (2 * (weightedFactorialNormSq n ϖ y ρ (K i) (X i) +
          weightedFactorialNormSq n ϖ y ρ (K i) (Y i))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_right
          (CycleWords.weightedFactorialNormSq_sub_le n ϖ y ρ _ _) _
    _ = 2 * (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (X i) +
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (Y i)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 2 * (ENNReal.ofReal a + ENNReal.ofReal b) := mul_le_mul_right (add_le_add hX hY) _
    _ = ENNReal.ofReal (2 * (a + b)) := by
        rw [← ENNReal.ofReal_add ha hb, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- Equal families have equal energies. -/
theorem family_energy_congr (π : ι → ℝ) (n : ℕ) (ϖ : ℝ) (y : Vec 2) (ρ : ℝ) (K : ι → ℕ)
    (X Y : ∀ i, PlaneHk Set.univ (K i) (h i)) (hXY : ∀ i, X i = Y i) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (X i) =
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y ρ (K i) (Y i) := by
  rw [funext hXY]

end Family

section Error

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The prepared norm of the localized datum at radius `ρ`. -/
def patchPrepared {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (π : ι → ℝ) (K : ι → ℕ) (ρ : ℝ) (f : ∀ i, TorusHk (K i) (h i)) : ℝ :=
  ∑ i, (π i)⁻¹ * factorialNormSq ρ
    (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)).val

omit [DecidableEq ι] in
theorem patchPrepared_nonneg {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (j : Fin 2 → Fin N) {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (ρ : ℝ)
    (f : ∀ i, TorusHk (K i) (h i)) : 0 ≤ patchPrepared hζ N hN j π K ρ f :=
  Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.2 (hπ i).le) (factorialNormSq_nonneg _ _)

omit [DecidableEq ι] in
/-- The `L²` norm of the slot-`0` localization is at most the prepared norm. -/
theorem loc0_sum_le_prepared {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (j : Fin 2 → Fin N) {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (ρ : ℝ)
    (f : ∀ i, TorusHk (K i) (h i)) :
    ∑ i, (π i)⁻¹ *
        ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le (K i)) (f i))‖ ^ 2 ≤
      patchPrepared hζ N hN j π K ρ f :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (loc0_norm_sq_le hζ N hN j (f i) ρ)
    (inv_nonneg.2 (hπ i).le)

/-- **The unweighted error of one patch**: the error of the two-block theorem plus the return of the seam's masked error. -/
theorem patch_error_unweighted (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    {Mb : ℕ} (hKM : ∀ i, K i ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (pout : ℕ) (CNp e2 : ℝ) (hCNp : 0 ≤ CNp) (he2 : 0 ≤ e2) (ξ : ∀ i, TorusHk (K i) (h i))
    (u : ∀ i, PlaneHk Set.univ (K i) (h i)) (uFsum : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hC2 : ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq r
        (u i - twoReturn hp hΛ hchart i (uFsum i)).val) ≤
      ENNReal.ofReal (e2 * patchPrepared hζ N hN j π K r ξ))
    (herr : weightedJetNorm π (pout : ℝ) Kmax (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (r / ocEpsilon q Λ m)
        (fun x a' wd z => if a' ≤ K x then
          planeJetOrder (uFsum x) a' wd z - orderedDerivative wd (Mc ξ x) z else 0) ≤
      ENNReal.ofReal CNp * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x))) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq 0
        (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) r (K i)
        (u i - twoReturn hp hΛ hchart i
          (truncatePlaneHk (hKM i) (realizeCellModel Mb Mc hsm hmem ξ i))) ≤
      ENNReal.ofReal (2 * (e2 + returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0 * CNp ^ 2) *
        patchPrepared hζ N hN j π K r ξ) := by
  have hc := returnConstant_nonneg Cchart (ocEpsilon q Λ (m - 1)) Kmax 0
  have hS := patchPrepared_nonneg hζ N hN j hp.hπ K r ξ
  have hseam := seam_error_return_le hW hΛ hchart hζ hp heE N hN j hyc hKM Mc hsm hmem pout CNp
    hCNp ξ uFsum herr
  have hsplit : ∀ i, u i - twoReturn hp hΛ hchart i
      (truncatePlaneHk (hKM i) (realizeCellModel Mb Mc hsm hmem ξ i)) =
      (u i - twoReturn hp hΛ hchart i (uFsum i)) + twoReturn hp hΛ hchart i
        (uFsum i - truncatePlaneHk (hKM i) (realizeCellModel Mb Mc hsm hmem ξ i)) := by
    intro i
    rw [map_sub]
    abel
  have hA : ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq 0
      (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
      (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) r (K i)
      (u i - twoReturn hp hΛ hchart i (uFsum i)) ≤
      ENNReal.ofReal (e2 * patchPrepared hζ N hN j π K r ξ) := by
    refine le_trans (le_of_eq ?_) hC2
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
      mul_nonneg (inv_nonneg.2 (hp.hπ i).le) (factorialNormSq_nonneg _ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [weightedFactorialNormSq_zero_moment, ENNReal.ofReal_mul (inv_nonneg.2 (hp.hπ i).le)]
  have hB : ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq 0
      (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
      (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) r (K i)
      (twoReturn hp hΛ hchart i
        (uFsum i - truncatePlaneHk (hKM i) (realizeCellModel Mb Mc hsm hmem ξ i))) ≤
      ENNReal.ofReal (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0 * CNp ^ 2 *
        patchPrepared hζ N hN j π K r ξ) :=
    hseam.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (loc0_sum_le_prepared hζ N hN j hp.hπ K r ξ) (mul_nonneg hc (sq_nonneg _))))
  refine (family_add_energy_le π 0 _ _ r K _ _ _ hsplit _ _ (mul_nonneg he2 hS)
    (mul_nonneg (mul_nonneg hc (sq_nonneg _)) hS) hA hB).trans (le_of_eq ?_)
  congr 1
  ring

/-- A sum of `π⁻¹ ofReal c (ofReal e x_i)` factors. -/
theorem sum_factor_le {ι' : Type*} [Fintype ι'] (π' : ι' → ℝ) (c e S : ℝ) (hc : 0 ≤ c)
    (X W : ι' → ℝ≥0∞) (hX : ∀ i, X i ≤ ENNReal.ofReal c * (ENNReal.ofReal e * W i))
    (hW : ENNReal.ofReal e * ∑ i, ENNReal.ofReal ((π' i)⁻¹) * W i ≤ ENNReal.ofReal S) :
    ∑ i, ENNReal.ofReal ((π' i)⁻¹) * X i ≤ ENNReal.ofReal (c * S) := by
  calc ∑ i, ENNReal.ofReal ((π' i)⁻¹) * X i
      ≤ ∑ i, ENNReal.ofReal ((π' i)⁻¹) * (ENNReal.ofReal c * (ENNReal.ofReal e * W i)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_right (hX i) _
    _ = ENNReal.ofReal c * (ENNReal.ofReal e * ∑ i, ENNReal.ofReal ((π' i)⁻¹) * W i) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal S := mul_le_mul_right hW _
    _ = ENNReal.ofReal (c * S) := (ENNReal.ofReal_mul hc).symm

/-- **The moments of the error of one patch** (no small factor). -/
theorem patch_error_moment (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    {Mb : ℕ} (hMb : Mb ≤ Jchart + 1) (hKM : ∀ i, K i ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (n' : ℕ) (m1 CM : ℝ) (hm1 : 0 ≤ m1) (hCM : 0 ≤ CM) (ξ : ∀ i, TorusHk (K i) (h i))
    (u' : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hG4 : ENNReal.ofReal (ocEpsilon q Λ m ^ 2) * ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n' (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
          (r / ocEpsilon q Λ m) (K i) (u' i) ≤
      ENNReal.ofReal (m1 * patchPrepared hζ N hN j π K r ξ))
    (hmodel : weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x))) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n'
        (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) r (K i)
        (twoReturn hp hΛ hchart i (u' i) - truncatePlaneHk (hKM i)
          (patchReturn hΛ hp Mb hMb i (realizeCellModel Mb Mc hsm hmem ξ i))) ≤
      ENNReal.ofReal (2 * (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax n' * m1 +
        patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM) *
          patchPrepared hζ N hN j π K r ξ) := by
  have hc := returnConstant_nonneg Cchart (ocEpsilon q Λ (m - 1)) Kmax n'
  have hS := patchPrepared_nonneg hζ N hN j hp.hπ K r ξ
  have hCmod : 0 ≤ patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM := by
    unfold patchModelConstant
    rw [preparationPieceFlowJetBudget_one]
    have := le_max_right (Cchart 0) 0
    positivity
  have hX := sum_factor_le π _ _ _ hc _ _
    (fun i => twoReturn_weighted_le hW hΛ hchart hp N j hyc n' hp.cov.pos.2.2.le
      (hp.cov.rho_e.trans heE) i (u' i)) hG4
  have hY := (model_moment_le π K hKM n' (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
    (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) hp.cov.pos.2.2.le hp.cov.rho_R
    (fun i => patchReturn hΛ hp Mb hMb i (realizeCellModel Mb Mc hsm hmem ξ i))).trans
    ((patch_model_bound hW hΛ hchart hζ hp N hN j hyc Mb hMb n' Mc hsm hmem CM hCM ξ
      hmodel).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (loc0_sum_le_prepared hζ N hN j hp.hπ K r ξ) hCmod)))
  refine (family_sub_energy_le π n' _ _ r K _ _ _ _ (mul_nonneg (mul_nonneg hc hm1) hS)
    (mul_nonneg hCmod hS) (by rw [← mul_assoc] at hX; exact hX) hY).trans (le_of_eq ?_)
  congr 1
  ring

/-- The radius conversion inside a price. -/
theorem price_radius_mono {c L Sr So : ℝ} (hc : 0 ≤ c) (h : Sr ≤ L * So) :
    c * Sr ≤ c * L * So := by
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h hc

/-- The last step of the weighted error: radius conversion and interpolation. -/
theorem patch_interp_final {ι' : Type u} [Fintype ι'] {h' : ι' → Type v}
    [∀ i, NormedAddCommGroup (h' i)] [∀ i, InnerProductSpace ℝ (h' i)]
    [∀ i, MeasurableSpace (h' i)] [∀ i, BorelSpace (h' i)] [∀ i, CompleteSpace (h' i)]
    (hI : MassInterpolationStatement.{u, v}) (π' : ι' → ℝ) (K' : ι' → ℕ) {n n' : ℕ}
    (hnn : n ≤ n') (hn' : 0 < n') (ϖ : ℝ) (y : Vec 2) (r : ℝ)
    (E : ∀ i, PlaneHk Set.univ (K' i) (h' i)) (a0 a1 L Sr So εB : ℝ) (ha0 : 0 ≤ a0)
    (ha1 : 0 ≤ a1) (hL : 0 ≤ L) (hSo : 0 ≤ So) (hrad : Sr ≤ L * So)
    (h0 : ∑ i, ENNReal.ofReal ((π' i)⁻¹) * weightedFactorialNormSq 0 ϖ y r (K' i) (E i) ≤
      ENNReal.ofReal (a0 * Sr))
    (h1 : ∑ i, ENNReal.ofReal ((π' i)⁻¹) * weightedFactorialNormSq n' ϖ y r (K' i) (E i) ≤
      ENNReal.ofReal (a1 * Sr))
    (hprice : (a0 * L) ^ (1 - (n : ℝ) / n') * (a1 * L) ^ ((n : ℝ) / n') ≤ εB ^ 2) :
    ∑ i, ENNReal.ofReal ((π' i)⁻¹) * weightedFactorialNormSq n ϖ y r (K' i) (E i) ≤
      ENNReal.ofReal (εB ^ 2 * So) := by
  have hsq : Real.sqrt (a0 * L) ^ 2 = a0 * L := Real.sq_sqrt (mul_nonneg ha0 hL)
  have h0' : ∑ i, ENNReal.ofReal ((π' i)⁻¹) * weightedFactorialNormSq 0 ϖ y r (K' i) (E i) ≤
      ENNReal.ofReal (Real.sqrt (a0 * L) ^ 2 * So) := by
    rw [hsq]
    exact h0.trans (ENNReal.ofReal_le_ofReal (price_radius_mono ha0 hrad))
  have h1' : ∑ i, ENNReal.ofReal ((π' i)⁻¹) * weightedFactorialNormSq n' ϖ y r (K' i) (E i) ≤
      ENNReal.ofReal (a1 * L * So) :=
    h1.trans (ENNReal.ofReal_le_ofReal (price_radius_mono ha1 hrad))
  rw [← hsq] at hprice
  exact patch_error_interp hI π' K' hnn hn' ϖ y r E So _ _ εB hSo (mul_nonneg ha1 hL) hprice h0' h1'

/-- The squared error price of the unweighted error (with the radius conversion). -/
def patchErrorPrice0 (Cchart : ℕ → ℝ) (E : ℝ) (Kmax : ℕ) (e2 CNp Lr : ℝ) : ℝ :=
  2 * (e2 + returnConstant Cchart E Kmax 0 * CNp ^ 2) * Lr ^ (2 * Kmax)

/-- The moment price of the error (with the radius conversion). -/
def patchErrorPrice1 (Cchart : ℕ → ℝ) (E : ℝ) (Kmax Mb n' : ℕ) (m1 CM Lr : ℝ) : ℝ :=
  2 * (returnConstant Cchart E Kmax n' * m1 + patchModelConstant Cchart E n' Mb CM) *
    Lr ^ (2 * Kmax)

/-- The model of one patch: the seam's cell model, realized, returned at `t_p` and truncated to
the required orders. -/
def patchModel (hΛ : 1 ≤ Λ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Mout : ℕ) {Mb : ℕ} (hMb : Mb ≤ Jchart + 1)
    (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume) :
    (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i)) :=
  (LinearMap.pi fun i => ((truncatePlaneHk (hmax i)).toLinearMap.comp
    (patchReturn hΛ hp Mb hMb i).toLinearMap).comp (LinearMap.proj i)) ∘ₗ
    realizeCellModel Mb Mc hsm hmem

theorem patchModel_apply (hΛ : 1 ≤ Λ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Mout : ℕ) {Mb : ℕ} (hMb : Mb ≤ Jchart + 1)
    (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (f : ∀ i, TorusHk (K i) (h i)) (i : ι) :
    patchModel hΛ hp Mout hMb hmax Mc hsm hmem f i =
      truncatePlaneHk (hmax i) (patchReturn hΛ hp Mb hMb i (realizeCellModel Mb Mc hsm hmem f i)) :=
  rfl

/-- The truncated model is the return of the truncated cell model. -/
theorem patchModel_truncate_eq (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (Mout : ℕ) {Mb : ℕ} (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (f : ∀ i, TorusHk (K i) (h i)) (i : ι) :
    truncatePlaneHk (le_max_right Mout (K i)) (patchModel hΛ hp Mout hMb hmax Mc hsm hmem f i) =
      twoReturn hp hΛ hchart i (truncatePlaneHk ((le_max_right Mout (K i)).trans (hmax i))
        (realizeCellModel Mb Mc hsm hmem f i)) :=
  (truncatePlaneHk_truncatePlaneHk _ _ _).trans
    (preparationWindowReferenceCellReturn_truncate hp.hprep hp.hcover _ _ _
      ((le_max_right Mout (K i)).trans (hmax i)) hMb _ _ _ _ _ _)

/-- The unweighted error of the patch model. -/
theorem patch_error_h0 (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (Mout : ℕ) {Mb : ℕ} (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (pout : ℕ) (CNp e2 : ℝ) (hCNp : 0 ≤ CNp) (he2 : 0 ≤ e2) (f : ∀ i, TorusHk (K i) (h i))
    (Ut u : ∀ i, PlaneHk Set.univ (K i) (h i)) (hU : ∀ i, Ut i = u i)
    (uFsum : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hC2 : ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq r
        (u i - twoReturn hp hΛ hchart i (uFsum i)).val) ≤
      ENNReal.ofReal (e2 * patchPrepared hζ N hN j π K r f))
    (herr : weightedJetNorm π (pout : ℝ) Kmax
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m)
        (fun x a' wd z => if a' ≤ K x then
          planeJetOrder (uFsum x) a' wd z - orderedDerivative wd (Mc f x) z else 0) ≤
      ENNReal.ofReal CNp * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) f x))) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq 0 (Real.sqrt (B * ocTauPP α q Λ m))⁻¹ (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) r (K i)
      (Ut i - truncatePlaneHk (le_max_right Mout (K i))
        (patchModel hΛ hp Mout hMb hmax Mc hsm hmem f i)) ≤
      ENNReal.ofReal (2 * (e2 + returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax 0 * CNp ^ 2) *
        patchPrepared hζ N hN j π K r f) :=
  (family_energy_congr π 0 _ _ r K _ _ fun i => congrArg₂ (· - ·) (hU i)
      (patchModel_truncate_eq hΛ hchart hp Mout hMb hmax Mc hsm hmem f i)).trans_le
    (patch_error_unweighted hW hΛ hchart hζ hp heE N hN j hyc
      (fun i => (le_max_right Mout (K i)).trans (hmax i)) Mc hsm hmem pout CNp e2 hCNp he2 f u
      uFsum hC2 herr)

/-- The moments of the error of the patch model. -/
theorem patch_error_h1 (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (Mout : ℕ) {Mb : ℕ} (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (n' : ℕ) (m1 CM : ℝ) (hm1 : 0 ≤ m1) (hCM : 0 ≤ CM) (f : ∀ i, TorusHk (K i) (h i))
    (Ut u' : ∀ i, PlaneHk Set.univ (K i) (h i)) (hU : ∀ i, Ut i = twoReturn hp hΛ hchart i (u' i))
    (hG4 : ENNReal.ofReal (ocEpsilon q Λ m ^ 2) * ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n' (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
          (r / ocEpsilon q Λ m) (K i) (u' i) ≤
      ENNReal.ofReal (m1 * patchPrepared hζ N hN j π K r f))
    (hmodel : weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc f x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) f x))) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n' (Real.sqrt (B * ocTauPP α q Λ m))⁻¹ (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) r (K i)
      (Ut i - truncatePlaneHk (le_max_right Mout (K i))
        (patchModel hΛ hp Mout hMb hmax Mc hsm hmem f i)) ≤
      ENNReal.ofReal (2 * (returnConstant Cchart (ocEpsilon q Λ (m - 1)) Kmax n' * m1 +
        patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM) *
          patchPrepared hζ N hN j π K r f) :=
  (family_energy_congr π n' _ _ r K _ _ fun i => congrArg₂ (· - ·) (hU i)
      (truncatePlaneHk_truncatePlaneHk _ _ _)).trans_le
    (patch_error_moment hW hΛ hchart hζ hp heE N hN j hyc hMb
      (fun i => (le_max_right Mout (K i)).trans (hmax i)) Mc hsm hmem n' m1 CM hm1 hCM f u'
      hG4 hmodel)

/-- **The weighted error of one patch.** -/
theorem patch_error_weighted (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q) (hΛ128 : 128 ≤ Λ)
    (hΛ : 1 ≤ Λ) (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (Mout : ℕ) {Mb : ℕ} (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (n n' pout : ℕ) (hnn : n ≤ n') (hn' : 0 < n') (CNp e2 m1 CM εB : ℝ) (hCNp : 0 ≤ CNp)
    (he2 : 0 ≤ e2) (hm1 : 0 ≤ m1) (hCM : 0 ≤ CM)
    (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : twoPhysical hp hζ N hN (fun k => (j k : ℤ)) uphys wphys)
    (uFsum : (∀ i, TorusHk (K i) (h i)) → ∀ i, PlaneHk Set.univ (K i) (h i))
    (hC2 : ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq r
        (uphys ξ i (twoTp α q Λ m l₀) - twoReturn hp hΛ hchart i (uFsum ξ i)).val) ≤
      ENNReal.ofReal (e2 * patchPrepared hζ N hN j π K r ξ))
    (herr : ∀ ξ, weightedJetNorm π (pout : ℝ) Kmax
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m)
        (fun x a' wd z => if a' ≤ K x then
          planeJetOrder (uFsum ξ x) a' wd z - orderedDerivative wd (Mc ξ x) z else 0) ≤
      ENNReal.ofReal CNp * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (uphys' : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys' : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol' : twoPhysical hp hζ N hN (fun k => (j k : ℤ)) uphys' wphys')
    (hG4 : ∀ ξ, ENNReal.ofReal (ocEpsilon q Λ m ^ 2) * ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n' (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
          (r / ocEpsilon q Λ m) (K i)
          (twoUHpost hp hΛ hchart uphys' ξ i (cellTime q Λ m ν (twoTp α q Λ m l₀))) ≤
      ENNReal.ofReal (m1 * patchPrepared hζ N hN j π K r ξ))
    (hmodel : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax e2 CNp
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ (1 - (n : ℝ) / n') *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb n' m1 CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ ((n : ℝ) / n') ≤
      εB ^ 2)
    (f : ∀ i, TorusHk (K i) (h i)) (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (W : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hU : IsCoupledWeakSolutionPlane ν tS (twoTp α q Λ m l₀) (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
      (fun _ _ => 0) (fun _ _ => 0) U W) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n
        (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) r (K i)
        (U i (twoTp α q Λ m l₀) - truncatePlaneHk (le_max_right Mout (K i))
          (patchModel hΛ hp Mout hMb hmax Mc hsm hmem f i)) ≤
      ENNReal.ofReal (εB ^ 2 * ∑ i, (π i)⁻¹ * factorialNormSq ρold
        (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)).val) := by
  obtain ⟨heE, -⟩ := hp.scales hq hΛ128 hg₀
  have hSold : 0 ≤ ∑ i, (π i)⁻¹ * factorialNormSq ρold
      (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)).val :=
    Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.2 (hp.hπ i).le) (factorialNormSq_nonneg _ _)
  have hrad : patchPrepared hζ N hN j π K r f ≤
      max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))) ^ (2 * Kmax) *
        ∑ i, (π i)⁻¹ * factorialNormSq ρold
          (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)).val :=
    prepared_radius_le hp
      (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
  have hc0 := returnConstant_nonneg Cchart (ocEpsilon q Λ (m - 1)) Kmax 0
  have hc1 := returnConstant_nonneg Cchart (ocEpsilon q Λ (m - 1)) Kmax n'
  have hCmod : 0 ≤ patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM := by
    unfold patchModelConstant
    rw [preparationPieceFlowJetBudget_one]
    have := le_max_right (Cchart 0) 0
    positivity
  have hU1 : ∀ i, U i (twoTp α q Λ m l₀) = uphys f i (twoTp α q Λ m l₀) :=
    hp.plane_eq_at_tp hq hΛ128 hg₀ hchart hmol
      (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
      (uphys f) (wphys f) (hsol f) U W hU
  have hU2 : ∀ i, U i (twoTp α q Λ m l₀) = twoReturn hp hΛ hchart i
      (twoUHpost hp hΛ hchart uphys' f i (cellTime q Λ m ν (twoTp α q Λ m l₀))) := fun i =>
    (hp.plane_eq_at_tp hq hΛ128 hg₀ hchart hmol
      (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
      (uphys' f) (wphys' f) (hsol' f) U W hU i).trans (physical_tp_eq_return hΛ hchart hp uphys' f i)
  exact patch_interp_final hI π K hnn hn' _ _ r _ _ _ _ _ _ εB
    (mul_nonneg (by norm_num) (add_nonneg he2 (mul_nonneg hc0 (sq_nonneg _))))
    (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hc1 hm1) hCmod))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) hSold hrad
    (patch_error_h0 hW hΛ hchart hζ hp heE N hN j hyc Mout hMb hmax Mc hsm hmem pout CNp e2 hCNp
      he2 f _ _ hU1 (uFsum f) (hC2 f) (herr f))
    (patch_error_h1 hW hΛ hchart hζ hp heE N hN j hyc Mout hMb hmax Mc hsm hmem n' m1 CM hm1 hCM
      f _ _ hU2 (hG4 f) (hmodel f)) hprice

end Error

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The model clause of one patch**.

- `cellModel_memLp`: the seam's model bound makes every derivative of order `≤ Mb` of the cell
  model square integrable (the moment norm of the cell datum is finite), so the cell model is
  realized as a plane carrier.
- `patchModel_bound_clause`: the model clause of `PatchSmoothModel` at radius `1 · R`, moment `n`
  and order `Mb`, with `C² = patchModelConstant … n' Mb CM` (`n ≤ n'`, the seam's moment order):
  truncation and the moment order only lower the energy, then the model bound of the patch.

For an empty index type the sums are `0`; for `CM = 0` the model is zero and `C = 0`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Clause

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The seam's model bound realizes the cell model. -/
theorem cellModel_memLp (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N) (Mb n' : ℕ) (CM : ℝ)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmodel : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (ξ : ∀ i, TorusHk (K i) (h i)) (x : ι) (a' : JetIndex2 Mb) :
    MemLp (orderedDerivative a'.2 (Mc ξ x)) 2 volume := by
  have hεpos : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hRpos : 0 < Real.sqrt (B * ocTauPP α q Λ m) :=
    Real.sqrt_pos.2 (mul_pos hp.cov.pos.2.1 (Construction.Stream.ocTauPP_pos hΛ))
  have hmom := twoV₀_momentNorm_sq hΛ hchart hζ hp N hN j ξ
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
  have hM : momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
      (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_pow two_ne_zero] at hmom
    exact ENNReal.ofReal_ne_top hmom.symm
  refine memLp_orderedDerivative_of_weightedJetNorm_ne_top π hp.hπ (n' : ℝ) (Nat.cast_nonneg _)
    Mb _ _ (inv_pos.2 (div_pos hεpos hRpos)) (Mc ξ) (hsm ξ)
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) (hmodel ξ)) x a'

/-- **The model clause of one patch.** -/
theorem patchModel_bound_clause (hW : WeightedPullbackStatement.{v}) (hΛ : 1 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (Mout : ℕ) {Mb : ℕ} (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmem : ∀ ξ x (a : JetIndex2 Mb), MemLp (orderedDerivative a.2 (Mc ξ x)) 2 volume)
    (n n' : ℕ) (hnn : n ≤ n') (CM : ℝ) (hCM : 0 ≤ CM)
    (hmodel : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (f : ∀ i, TorusHk (K i) (h i)) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n
        (Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j)
        (1 * Real.sqrt (B * ocTauPP α q Λ m)) Mb
        (patchModel hΛ hp Mout hMb hmax Mc hsm hmem f i) ≤
      ENNReal.ofReal (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM) ^ 2 *
        ∑ i, (π i)⁻¹ *
          ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le (K i)) (f i))‖ ^ 2) := by
  have hCmod : 0 ≤ patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM := by
    unfold patchModelConstant
    rw [preparationPieceFlowJetBudget_one]
    have := le_max_right (Cchart 0) 0
    positivity
  rw [Real.sq_sqrt hCmod, one_mul]
  refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_right
    ((weightedFactorialNormSq_truncate_le (hmax i) _ n _ _ _ Mb).trans
      (weightedFactorialNormSq_moment_mono hnn _ _ _ _ _)) _) ?_
  exact patch_model_bound hW hΛ hchart hζ hp N hN j hyc Mb hMb n' Mc hsm hmem CM hCM f (hmodel f)

/-- **The two-block price on the prepared norm**: with the remaining factor of the two-block price bounded by `q₂`,
the error of the two-block theorem is at most `C_comp² q₂ dP` times the prepared norm at radius `r`. -/
theorem c2_error_price_le (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m)) (Npre : ℕ)
    (Cpost Cseam Cfirst εlow εhigh εpost : ℝ≥0∞) (q2 : ℝ) (hq2 : 0 ≤ q2)
    (hQ2 : 2 * (Cpost * Cseam * εlow + εpost * (2 * (Cfirst + εhigh))) ≤ ENNReal.ofReal q2)
    (ξ : ∀ i, TorusHk (K i) (h i)) (X : ℝ≥0∞)
    (hX : X ≤ twoBlockOriginalEnergyPrice
      (ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
        (Jchart + 1) * |ocEpsilon q Λ m|) ^ 2)) Cpost Cseam Cfirst εlow εhigh εpost *
      twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ) :
    X ≤ ENNReal.ofReal (compositionFactorialNormBound (preparationFlowJetConstant Cchart)
        (Jchart + 1) ^ 2 * q2 * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre *
      patchPrepared hζ N hN j π K r ξ) := by
  have hE := twoEin_le hΛ hchart hζ hp heE N hN j hyc hNR Npre ξ
  have hdP := datumEnergyPrice_nonneg Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre
  have hS := patchPrepared_nonneg hζ N hN j hp.hπ K r ξ
  refine hX.trans ?_
  unfold twoBlockOriginalEnergyPrice
  rw [mul_pow, sq_abs, ENNReal.ofReal_mul (sq_nonneg _)]
  calc ENNReal.ofReal (compositionFactorialNormBound (preparationFlowJetConstant Cchart)
          (Jchart + 1) ^ 2) * ENNReal.ofReal (ocEpsilon q Λ m ^ 2) * 2 *
        (Cpost * Cseam * εlow + εpost * (2 * (Cfirst + εhigh))) *
        twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ
      = ENNReal.ofReal (compositionFactorialNormBound (preparationFlowJetConstant Cchart)
          (Jchart + 1) ^ 2) * (2 * (Cpost * Cseam * εlow + εpost * (2 * (Cfirst + εhigh)))) *
        (ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
          twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ) := by ring
    _ ≤ ENNReal.ofReal (compositionFactorialNormBound (preparationFlowJetConstant Cchart)
          (Jchart + 1) ^ 2) * ENNReal.ofReal q2 *
        ENNReal.ofReal (datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre *
          patchPrepared hζ N hN j π K r ξ) :=
        mul_le_mul' (mul_le_mul_right hQ2 _) hE
    _ = _ := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **The price of the moment bound on the prepared norm.** -/
theorem moment_price_le (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m)) (Npre : ℕ)
    (Cmom : ℝ≥0∞) (qm : ℝ) (hqm : 0 ≤ qm) (hQm : Cmom ≤ ENNReal.ofReal qm)
    (ξ : ∀ i, TorusHk (K i) (h i)) (X : ℝ≥0∞)
    (hX : X ≤ Cmom * twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ) :
    ENNReal.ofReal (ocEpsilon q Λ m ^ 2) * X ≤
      ENNReal.ofReal (qm * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre *
        patchPrepared hζ N hN j π K r ξ) := by
  have hE := twoEin_le hΛ hchart hζ hp heE N hN j hyc hNR Npre ξ
  have hdP := datumEnergyPrice_nonneg Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre
  calc ENNReal.ofReal (ocEpsilon q Λ m ^ 2) * X
      ≤ ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
          (Cmom * twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ) :=
        mul_le_mul_right hX _
    _ = Cmom * (ENNReal.ofReal (ocEpsilon q Λ m ^ 2) *
          twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ) := by ring
    _ ≤ ENNReal.ofReal qm * ENNReal.ofReal (datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1))
          Jchart Npre * patchPrepared hζ N hN j π K r ξ) := mul_le_mul' hQm hE
    _ = _ := by
        rw [← ENNReal.ofReal_mul hqm]
        congr 1
        ring

end Clause

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **One patch from the two-block theorem, the seam and the moments**.

`PatchModelClausesK`: the slot-`K` part of `PatchSmoothModel` (a linear model on slot-`K` data with
the weighted model bound and the weighted physical error).

`patchModelClausesK_of_outputs`: for the premises recentred at the transported patch centre, the
body of the two-block theorem (word chains, physical solution, error), the seam's body (cell model, model bound,
masked error; the support of the cell datum) and the moment body give the slot-`K`
part, once the prices satisfy the three price premises (the remaining factor of the two-block price `≤ q₂`, the moment
price `≤ q_m`, and the interpolated price `≤ ε²`), which the price ledger discharges.

For an empty index type every sum is `0` and `P = 0` works. The letters' strengths are those of
`BlockLettersStatement` (`CL g`, `CL Cth Θ`), shared by the two-block theorem and the seam. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section K

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The clauses of a slot-`K` patch model `P`: the model bound and the physical error. -/
def PatchModelClausesK {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Mout Mb D : ℕ) (C c ε : ℝ) (n : ℕ)
    (π : ι → ℝ) (K : ι → ℕ) (ν tS tp ρs ρold R : ℝ) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (y : Vec 2) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (P : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (max Mout (K i)) (h i))) :
    Prop :=
    (∀ f, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ y (c * R) Mb (P f i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ *
        ‖spatialPatchLocalizationCLM hζ N hN j (truncateTorusHk (Nat.zero_le (K i)) (f i))‖ ^ 2)) ∧
    (∀ (f : ∀ i, TorusHk (K i) (h i)) (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (W : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν tS tp b D K A
        (fun i => spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i))
        (fun _ _ => 0) (fun _ _ => 0) U W →
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n R⁻¹ y ρs (K i)
          (U i tp - truncatePlaneHk (le_max_right Mout (K i)) (P f i)) ≤
        ENNReal.ofReal (ε ^ 2 * ∑ i, (π i)⁻¹ * factorialNormSq ρold
          (spatialPatchLocalization hζ N hN (fun k => (j k : ℤ)) (K i) (f i)).val))

end K

section Outputs

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- **The clauses of the slot-`K` patch model from the outputs of the two-block theorem, the seam and the
moments**: the model is `patchModel` of the seam's cell model. -/
theorem patchModelClausesK_of_outputs (hI : MassInterpolationStatement.{u, v})
    (hW : WeightedPullbackStatement.{v}) {s : ℝ} (hq : IsAdmissibleQ α s q) (hΛ128 : 128 ≤ Λ)
    (hΛ : 1 ≤ Λ) (hg₀ : g₀ ≤ 1 / 32) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (hζ : IsFastProfile ζ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N)
    (hyc : y₀ = streamFlow (Φ (m - 1)) hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      (spatialPatchCentre N (fun k => (j k : ℤ))) tS)
    (hNR : 8 ≤ (N : ℝ) * Real.sqrt (B * ocTauPP α q Λ m))
    (Mout : ℕ) {Mb : ℕ} (hMb : Mb ≤ Jchart + 1) (hmax : ∀ i, max Mout (K i) ≤ Mb)
    (n n' Npre : ℕ) (hnn : n ≤ n') (hn' : 0 < n') (CM CNp εB : ℝ) (hCM : 0 ≤ CM) (hCNp : 0 ≤ CNp)
    -- the two-block theorem
    (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : twoPhysical hp hζ N hN (fun k => (j k : ℤ)) uphys wphys)
    (uFsum : (∀ i, TorusHk (K i) (h i)) → ∀ i, PlaneHk Set.univ (K i) (h i))
    (Cpost Cseam Cfirst εlow εhigh εpost : ℝ≥0∞) (q2 : ℝ) (hq2 : 0 ≤ q2)
    (hQ2 : 2 * (Cpost * Cseam * εlow + εpost * (2 * (Cfirst + εhigh))) ≤ ENNReal.ofReal q2)
    (herrC2 : ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq r
        (uphys ξ i (twoTp α q Λ m l₀) - twoReturn hp hΛ hchart i (uFsum ξ i)).val) ≤
      twoBlockOriginalEnergyPrice
        (ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
          (Jchart + 1) * |ocEpsilon q Λ m|) ^ 2)) Cpost Cseam Cfirst εlow εhigh εpost *
        twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ)
    -- the seam
    (Mc : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (hsm : ∀ ξ x (k : ℕ), ContDiff ℝ k (Mc ξ x))
    (hmodel : ∀ ξ, weightedJetNorm π (n' : ℝ) Mb
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))⁻¹
        (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
      ENNReal.ofReal CM * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    (herr : ∀ ξ, weightedJetNorm π (n' : ℝ) Kmax
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m)
        (fun x a' wd z => if a' ≤ K x then
          planeJetOrder (uFsum ξ x) a' wd z - orderedDerivative wd (Mc ξ x) z else 0) ≤
      ENNReal.ofReal CNp * momentNorm π 0 (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
        (fun x => planeValue (twoV₀ hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) ξ x)))
    -- the moments
    (uphys' : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys' : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol' : twoPhysical hp hζ N hN (fun k => (j k : ℤ)) uphys' wphys')
    (Cmom : ℝ≥0∞) (qm : ℝ) (hqm : 0 ≤ qm) (hQm : Cmom ≤ ENNReal.ofReal qm)
    (hmom : ∀ ξ, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n' (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
          (r / ocEpsilon q Λ m) (K i)
          (twoUHpost hp hΛ hchart uphys' ξ i (cellTime q Λ m ν (twoTp α q Λ m l₀))) ≤
      Cmom * twoEin hp hΛ hchart hζ N hN (fun k => (j k : ℤ)) Npre ξ)
    -- the price
    (hprice : patchErrorPrice0 Cchart (ocEpsilon q Λ (m - 1)) Kmax
        (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) ^ 2 * q2 *
          datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CNp
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ (1 - (n : ℝ) / n') *
      patchErrorPrice1 Cchart (ocEpsilon q Λ (m - 1)) Kmax Mb n'
        (qm * datumEnergyPrice Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre) CM
        (max 1 (Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)))) ^ ((n : ℝ) / n') ≤
      εB ^ 2) :
    PatchModelClausesK hζ Mout Mb D
      (Real.sqrt (patchModelConstant Cchart (ocEpsilon q Λ (m - 1)) n' Mb CM)) 1 εB n π K ν tS
      (twoTp α q Λ m l₀) r ρold (Real.sqrt (B * ocTauPP α q Λ m)) N hN j
      (patchOutputCentre (Φ (m - 1)) hφ tS (twoTp α q Λ m l₀) N j) (streamVel (Φ m))
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (patchModel hΛ hp Mout hMb hmax Mc hsm
        (cellModel_memLp hΛ hchart hζ hp N hN j Mb n' CM Mc hsm hmodel)) := by
  obtain ⟨heE, -⟩ := hp.scales hq hΛ128 hg₀
  have hdP := datumEnergyPrice_nonneg Cchart (ocEpsilon q Λ (m - 1)) Jchart Npre
  have hmem := cellModel_memLp hΛ hchart hζ hp N hN j Mb n' CM Mc hsm hmodel
  refine ⟨fun f => patchModel_bound_clause hW hΛ
    hchart hζ hp N hN j hyc Mout hMb hmax Mc hsm hmem n n' hnn CM hCM hmodel f,
    fun f U W hU => ?_⟩
  exact patch_error_weighted hI hW hq hΛ128 hΛ hg₀ hchart hmol hζ hp N hN j hyc Mout hMb hmax Mc
    hsm hmem n n' n' hnn hn' CNp _ _ CM εB hCNp
    (mul_nonneg (mul_nonneg (sq_nonneg _) hq2) hdP) (mul_nonneg hqm hdP) hCM uphys wphys hsol
    uFsum (fun ξ => c2_error_price_le hΛ hchart hζ hp heE N hN j hyc hNR Npre Cpost Cseam Cfirst
      εlow εhigh εpost q2 hq2 hQ2 ξ _ (herrC2 ξ)) herr uphys' wphys' hsol'
    (fun ξ => moment_price_le hΛ hchart hζ hp heE N hN j hyc hNR Npre Cmom qm hqm hQm ξ _
      (hmom ξ)) hmodel hprice f U W hU

end Outputs

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The interpolated price of the patch error**.

The constants of the return, the model and the cell datum depend on the chart jets only through
`B₁ = 1 + max (Cchart 0) 0 / 2` (`preparationPieceFlowJetBudget_one`), so they do not depend on the
level. With the remaining factor `q₂ ≤ K₂ E^k`, the seam price `CNp ≤ CN Cs E^{a_s}` (`k ≤ 2 a_s`),
the moment constant `q_m`, and the radius ratio `Lr = max 1 (Crat E^{-qδ}) ≤ max 1 Crat · E^{-qδ}`,
the interpolated price is at most `CP² E^{2P}` once `2P ≤ (1-θ)(k - 2qδ Kmax) - θ 2qδ Kmax`.

For `θ = 0` only the unweighted price remains, and for `Crat ≤ 1` one has `Lc = 1`. -/

theorem returnConstant_level (Cchart : ℕ → ℝ) (E E' : ℝ) (Kmax n : ℕ) :
    returnConstant Cchart E Kmax n = returnConstant Cchart E' Kmax n := by
  unfold returnConstant
  rw [preparationPieceFlowJetBudget_one, preparationPieceFlowJetBudget_one]

theorem patchModelConstant_level (Cchart : ℕ → ℝ) (E E' : ℝ) (n Mb : ℕ) (CM : ℝ) :
    patchModelConstant Cchart E n Mb CM = patchModelConstant Cchart E' n Mb CM := by
  unfold patchModelConstant
  rw [preparationPieceFlowJetBudget_one, preparationPieceFlowJetBudget_one]

theorem datumEnergyPrice_level (Cchart : ℕ → ℝ) (E E' : ℝ) (Jchart N : ℕ) :
    datumEnergyPrice Cchart E Jchart N = datumEnergyPrice Cchart E' Jchart N := by
  unfold datumEnergyPrice
  rw [preparationPieceFlowJetBudget_one, preparationPieceFlowJetBudget_one]

/-- The radius ratio in powers of `E`. -/
theorem radiusRatio_le {E Crat b : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (hb : 0 ≤ b) :
    max 1 (Crat * E ^ (-b)) ≤ max 1 Crat * E ^ (-b) := by
  have h1 : 1 ≤ E ^ (-b) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE hE1 (by linarith)
  have hm : 1 ≤ max 1 Crat := le_max_left _ _
  refine max_le (by nlinarith) ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

/-- **The interpolated price of the patch error.** -/
theorem b1_price_bound {E q2 K2 k CNp CN Cs as cb dP rc0 rc1 qm Cmod Crat qδ P θ : ℝ}
    (Kmax : ℕ) (hE : 0 < E) (hE1 : E ≤ 1) (hq2 : 0 ≤ q2) (hK2 : 0 ≤ K2)
    (hq2E : q2 ≤ K2 * E ^ k) (hCNp0 : 0 ≤ CNp)
    (hCNp : CNp ≤ CN * (Cs * E ^ as)) (hk : k ≤ 2 * as) (hdP : 0 ≤ dP)
    (hrc0 : 0 ≤ rc0) (hrc1 : 0 ≤ rc1) (hqm : 0 ≤ qm) (hCmod : 0 ≤ Cmod) (hqδ : 0 ≤ qδ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : 2 * P ≤ (1 - θ) * (k - 2 * qδ * Kmax) - θ * (2 * qδ * Kmax)) :
    (2 * (cb ^ 2 * q2 * dP + rc0 * CNp ^ 2) * max 1 (Crat * E ^ (-qδ)) ^ (2 * Kmax)) ^ (1 - θ) *
      (2 * (rc1 * (qm * dP) + Cmod) * max 1 (Crat * E ^ (-qδ)) ^ (2 * Kmax)) ^ θ ≤
    ((2 * (cb ^ 2 * K2 * dP + rc0 * (CN * Cs) ^ 2) * max 1 Crat ^ (2 * Kmax)) ^ (1 - θ) *
      (2 * (rc1 * (qm * dP) + Cmod) * max 1 Crat ^ (2 * Kmax)) ^ θ) * E ^ (2 * P) := by
  have hEp (x : ℝ) : 0 < E ^ x := Real.rpow_pos_of_pos hE x
  have hEk2 : E ^ (2 * as) ≤ E ^ k := Real.rpow_le_rpow_of_exponent_ge hE hE1 hk
  have hCNp2 : CNp ^ 2 ≤ (CN * Cs) ^ 2 * E ^ k := by
    have h := pow_le_pow_left₀ hCNp0 hCNp 2
    have he : (CN * (Cs * E ^ as)) ^ 2 = (CN * Cs) ^ 2 * E ^ (2 * as) := by
      rw [mul_comm 2 as, Real.rpow_mul hE.le]
      norm_num
      ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left hEk2 (sq_nonneg _))
  have hx₀ : 2 * (cb ^ 2 * q2 * dP + rc0 * CNp ^ 2) ≤
      2 * (cb ^ 2 * K2 * dP + rc0 * (CN * Cs) ^ 2) * E ^ k := by
    have h1 : cb ^ 2 * q2 * dP ≤ cb ^ 2 * (K2 * E ^ k) * dP :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2E (sq_nonneg _)) hdP
    have h2 : rc0 * CNp ^ 2 ≤ rc0 * ((CN * Cs) ^ 2 * E ^ k) :=
      mul_le_mul_of_nonneg_left hCNp2 hrc0
    nlinarith
  exact price_interp_final Kmax hE hE1 (by positivity) (by positivity) (by positivity)
    (by positivity) hx₀ le_rfl (le_max_left _ _) (radiusRatio_le hE hE1 hqδ) hθ0 hθ1 hP

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **One patch from the bodies of the two-block theorem, the seam and the moments**.

For the premises recentred at the transported patch centre: the body of the two-block theorem at the quiet set
`ocTrimmedQuietTimes` (core outside by `nonQuietCore`, fast independence by the premises) with the
letters of `BlockLettersStatement`'s strengths, the seam's body fed with the word chains of the two-block theorem (support of the cell datum by
the support statement with `Cs = (1 + max (Cchart 0) 0 / 2)/8`), and the moment body give the slot-`K` part of the
patch, under the scale premises of the three bodies and the price premises.

The remarks on degenerate inputs are those of `patchModelClausesK_of_outputs`. The letters of the
two-block theorem and the seam coincide by construction (`CL g` and `CL Cth Θ`). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev Set
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
  AVRegularity.CycleReference
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Bodies

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The trimmed quiet set of the premises has the core property used by the two-block theorem. -/
theorem JointPremisesGen.coreOutside (hΛ : 1 ≤ Λ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) :
    IsCoreOutside α q Λ m F tS (tS + 2 * ocTauPP α q Λ m) (ocTrimmedQuietTimes α q Λ ζ m) :=
  nonQuietCore.{u, v, w, x} α q Λ m hΛ ζ (Φ (m - 1)) hφ tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage
    Npad l₀ P F hp.hprep.schedule

end Bodies

end AVRegularity.CycleJointProofs.Assembly
end
end
