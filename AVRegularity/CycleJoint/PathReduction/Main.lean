-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PathReduction.Blocks
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleComparison.Error.WeakSolution
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.CycleJointProofs.PathReduction

/-! Mass Schur control of the finite path error. -/

/-- Scalar positive majorants control the original inverse-mass square norm. -/
theorem massScalarSchur {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ θ)
    (x y : ι → ℝ) (hy : ∀ v, 0 ≤ y v)
    (hbound : ∀ v, y v ≤ ∑ u, C * A v u * x u) :
    Real.sqrt (∑ v, (π v)⁻¹ * y v ^ 2) ≤
      C * θ * Real.sqrt (∑ u, (π u)⁻¹ * x u ^ 2) := by
  let b := massConjugatedMatrix π A
  have hb (v u : ι) : 0 ≤ b v u := mul_nonneg (Real.sqrt_nonneg _) (hA v u)
  have hnormalized (v : ι) : y v / Real.sqrt (π v) ≤
      ∑ u, (C * b v u) * (x u / Real.sqrt (π u)) := by
    apply (div_le_div_of_nonneg_right (hbound v) (Real.sqrt_nonneg _)).trans_eq
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun u _ => mass_normalized_block_bound_identity π hπ v u C _ _)
  have hr (v : ι) : ∑ u, C * b v u ≤ C * θ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hrow v) hC
  have hc (u : ι) : ∑ v, C * b v u ≤ C * θ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcol u) hC
  have hs := KernelEnergy.finiteRootSchur (fun v u => C * b v u)
    (fun u => x u / Real.sqrt (π u)) (fun v => y v / Real.sqrt (π v))
    1 (C * θ) (by norm_num) (fun v u => mul_nonneg hC (hb v u)) hr hc
    (fun v => ⟨div_nonneg (hy v) (Real.sqrt_nonneg _), by
      simpa only [one_mul] using hnormalized v⟩)
  simp only [one_mul, mass_normalized_square π hπ] at hs
  have hh := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hC hθ)] at hh
  exact hh

/-- The family-independent price for summing lengths through the depth. -/
def pathErrorFactor (Cth : ℝ) (H : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (H + 1), (max Cth 0 + 1) ^ n

/-- The length-zero summand makes the error factor at least one. -/
theorem pathErrorFactor_one_le (Cth : ℝ) (H : ℕ) : 1 ≤ pathErrorFactor Cth H := by
  have hh := Finset.single_le_sum
    (s := Finset.range (H + 1)) (f := fun n => (max Cth 0 + 1) ^ n)
    (fun n _ => pow_nonneg (add_nonneg (le_max_right Cth 0) zero_le_one) n)
    (Finset.mem_range.mpr (Nat.zero_lt_succ H))
  simpa only [pathErrorFactor, pow_zero] using hh

/-- A bounded Schur scale is dominated by a nonnegative family-independent price. -/
theorem envelope_schur_scale_le (Cth Θ : ℝ) (hΘ₀ : 0 ≤ Θ) (hΘ₁ : Θ ≤ 1) :
    Cth * Θ ≤ max Cth 0 + 1 := by
  calc
    Cth * Θ ≤ max Cth 0 * Θ := mul_le_mul_of_nonneg_right (le_max_left _ _) hΘ₀
    _ ≤ max Cth 0 * 1 := mul_le_mul_of_nonneg_left hΘ₁ (le_max_right _ _)
    _ ≤ max Cth 0 + 1 := by rw [mul_one]; exact le_add_of_nonneg_right zero_le_one

/-- The sum of positive matrix powers prices every path length through the depth. -/
def pathPowerMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (H : ℕ) :
    Matrix ι ι ℝ := ∑ n ∈ Finset.range (H + 1), A ^ n

/-- Every entry of the path-power matrix is nonnegative. -/
theorem pathPowerMatrix_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (H : ℕ) (v u : ι) :
    0 ≤ pathPowerMatrix A H v u := by
  simp only [pathPowerMatrix, Matrix.sum_apply]
  exact Finset.sum_nonneg (fun n _ => positiveMatrix_pow_nonneg A hA n v u)

/-- The power-sum matrix retains the row Schur price. -/
theorem pathPowerMatrix_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (Cth : ℝ) (H : ℕ)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ max Cth 0 + 1) (v : ι) :
    ∑ u, massConjugatedMatrix π (pathPowerMatrix A H) v u ≤ pathErrorFactor Cth H := by
  simp only [massConjugatedMatrix, pathPowerMatrix, Matrix.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun n _ => massMatrix_pow_row_sum π hπ A hA (max Cth 0 + 1)
    (add_nonneg (le_max_right Cth 0) zero_le_one) hrow n v)

/-- The power-sum matrix retains the column Schur price. -/
theorem pathPowerMatrix_col {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (Cth : ℝ) (H : ℕ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ max Cth 0 + 1) (u : ι) :
    ∑ v, massConjugatedMatrix π (pathPowerMatrix A H) v u ≤ pathErrorFactor Cth H := by
  simp only [massConjugatedMatrix, pathPowerMatrix, Matrix.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun n _ => massMatrix_pow_col_sum π hπ A hA (max Cth 0 + 1)
    (add_nonneg (le_max_right Cth 0) zero_le_one) hcol n u)

/-- Enlarging the common error price preserves each raw triangular clause. -/
theorem rawTriangularModel_error_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Mout H : ℕ) (A : Matrix ι ι ℝ)
    (E Pacc ρm C CP CP' : ℝ) (hE : 0 ≤ E) (hCP : CP ≤ CP')
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (hm : IsRawTriangularModel K Mout H F A E Pacc ρm C CP Pd Pg) :
    IsRawTriangularModel K Mout H F A E Pacc ρm C CP' Pd Pg := by
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2⟩
  intro v f
  exact (hm.2.1 v f).trans (mul_le_mul_of_nonneg_right
    (add_le_add_right (mul_le_mul_of_nonneg_right hCP (Real.rpow_nonneg hE _)) 1)
    (Real.sqrt_nonneg _))

/-- A linear projection commutes with subtraction of finite nested sums. -/
theorem sub_nested_sum_map {I : Type*} {J : I → Type*} [∀ i, Fintype (J i)]
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : F →ₗ[ℝ] E) (S : Finset I) (u : ∀ i, J i → E) (f : ∀ i, J i → F) :
    (∑ i ∈ S, ∑ j, u i j) - L (∑ i ∈ S, ∑ j, f i j) =
      ∑ i ∈ S, ∑ j, (u i j - L (f i j)) := by
  simp only [map_sum, Finset.sum_sub_distrib]

/-- Weighted path sums over all retained lengths are priced by the power-sum matrix. -/
theorem path_weighted_majorant_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (H : ℕ) (v : ι) (G : ι → ℝ) (D : ℝ) :
    (∑ n ∈ Finset.range (H + 1), ∑ p : Incoming ι n,
      D * incomingWeight A v p * G (incomingVertices v p 0)) =
      ∑ u, D * pathPowerMatrix A H v u * G u := by
  simp_rw [incomingVertices_first, mul_assoc, ← Finset.mul_sum, incomingWeight_majorant_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [pathPowerMatrix, Matrix.sum_apply]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

universe u v w x

variable (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)

variable {α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
  Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold}

variable (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)


variable (hq : 1 < q) (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
  (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)



variable (Mout : ℕ) (C CP c Pacc : ℝ)
variable (R : PathCoreCollection F actual K Mout H A ν (ocEpsilon q Λ m)
  (ocEpsilon q Λ (m - 1)) tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) (ocRhoMol α q Λ m cMol ν) ρold (c * Real.sqrt (B * ocTauPP α q Λ m)) Pacc C CP
  (streamVel (Φ m)))

/-- Carrier identifications preserve the exact retained path error norm. -/
theorem retained_path_error_norm {n : ℕ} (v : ι) (p : Incoming ι n)
    (hp : IncomingValid F A v p) (hn : n ≤ H) (f : ∀ i, TorusHk (K i) (h i)) :
    torusHkNorm (ocRhoMol α q Λ m cMol ν) (le_refl (K v))
      (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) -
        truncateTorusHk (le_max_right Mout (K v))
          (pathResponse R v p hn (fun i => truncateTorusHk (Nat.zero_le _) (f i)))) =
      torusHkNorm (ocRhoMol α q Λ m cMol ν)
        (le_refl (K (incomingVertices v p (Fin.last n))))
        ((incomingChain hprem hq hΛ hζ hchart hmol v p f).u (Fin.last n) (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) -
          truncateTorusHk (le_max_right Mout _)
            ((R n v p hp hn).corner (truncateTorusHk (Nat.zero_le _) (f (incomingVertices v p 0))))) := by
  rw [pathResponse, dite_eq_left hp]
  exact torusVertexCast_error_norm K Mout _ v (incomingVertices_last v p)
    (ocRhoMol α q Λ m cMol ν) _ _

/-- The core's physical error at one retained path has exactly its path weight. -/
theorem retained_path_error {n : ℕ} (v : ι) (p : Incoming ι n)
    (hp : IncomingValid F A v p) (hn : n ≤ H)
    (f : ∀ i, TorusHk (K i) (h i)) (Fv : ι → ℝ)
    (hf : ∀ i, torusHkNorm ρold (le_refl (K i)) (f i) ≤ Fv i) :
    torusHkNorm (ocRhoMol α q Λ m cMol ν) (le_refl (K v))
      (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) -
        truncateTorusHk (le_max_right Mout (K v))
          (pathResponse R v p hn (fun i => truncateTorusHk (Nat.zero_le _) (f i)))) ≤
      CP * ocEpsilon q Λ (m - 1) ^ Pacc * incomingWeight A v p * Fv (incomingVertices v p 0) := by
  let S := incomingChain hprem hq hΛ hζ hchart hmol v p f
  let core := R n v p hp hn
  have hpos := fun k => (incomingVertices_edges F A v p hp k).2
  have htp := (preparation_endpoint hprem hΛ).1
  have hs := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left htp.2 S.solution
  have hh := core.corner_error_single (pathMass_pos (incomingVertices v p) A hpos)
    (pathMass_first (incomingVertices v p) A) (f (incomingVertices v p 0))
    (Fv (incomingVertices v p 0)) (hf _) S.u S.w hs
  calc
    _ = torusHkNorm (ocRhoMol α q Λ m cMol ν)
        (le_refl (K (incomingVertices v p (Fin.last n))))
        (S.u (Fin.last n) (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) - truncateTorusHk (le_max_right Mout _)
          (core.corner (truncateTorusHk (Nat.zero_le _) (f (incomingVertices v p 0))))) :=
      retained_path_error_norm hprem hq hΛ hζ hchart hmol Mout C CP c Pacc R v p hp hn f
    _ ≤ Real.sqrt (pathMass (incomingVertices v p) A (Fin.last n)) *
        (CP * ocEpsilon q Λ (m - 1) ^ Pacc * Fv (incomingVertices v p 0)) := hh
    _ = _ := by
      rw [pathMass_last_sqrt (incomingVertices v p) A hpos, pathProduct_incomingVertices A v p]
      ring

/-- Invalid paths cost zero; retained paths have the core's exact product error price. -/
theorem path_error_bound (hCP : 0 ≤ CP) (hA : ∀ v u, 0 ≤ A v u)
    {n : ℕ} (v : ι) (p : Incoming ι n) (hn : n ≤ H)
    (f : ∀ i, TorusHk (K i) (h i)) (Fv : ι → ℝ)
    (hf : ∀ i, torusHkNorm ρold (le_refl (K i)) (f i) ≤ Fv i) :
    torusHkNorm (ocRhoMol α q Λ m cMol ν) (le_refl (K v))
      (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) -
        truncateTorusHk (le_max_right Mout (K v))
          (truncatedPathResponse R v p (fun i => truncateTorusHk (Nat.zero_le _) (f i)))) ≤
      CP * ocEpsilon q Λ (m - 1) ^ Pacc * incomingWeight A v p * Fv (incomingVertices v p 0) := by
  classical
  rw [truncatedPathResponse, dite_eq_left hn]
  by_cases hp : IncomingValid F A v p
  · exact retained_path_error hprem hq hΛ hζ hchart hmol Mout C CP c Pacc R v p hp hn f Fv hf
  · have htp := (preparation_endpoint hprem hΛ).1
    have hz := incoming_invalid_trajectory_zero hprem hq hΛ hζ hchart hmol v p f hp
      (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ⟨htp.1.le, htp.2⟩
    rw [pathResponse, dite_eq_right hp, hz, map_zero, sub_self,
      CycleComparison.Reconstruction.torusHkNorm_zero]
    have hE := (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le
    exact mul_nonneg (mul_nonneg (mul_nonneg hCP (Real.rpow_nonneg hE Pacc))
      (incomingWeight_nonneg A hA v p)) ((Real.sqrt_nonneg _).trans (hf _))

/-- The physical error is precisely the sum of its path errors for the same core operators. -/
theorem family_path_error_sum (f : ∀ i, TorusHk (K i) (h i))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionTorus ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
      (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u w) (v : ι) :
    u v (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) - truncateTorusHk (le_max_right Mout (K v))
      (jointOperator K Mout H (pathDiagonalBlock R) (pathSourceBlock R)
        (fun i => truncateTorusHk (Nat.zero_le _) (f i)) v) =
      ∑ n ∈ Finset.range (H + 1), ∑ p : Incoming ι n,
        (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f
          (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) -
          truncateTorusHk (le_max_right Mout (K v))
            (truncatedPathResponse R v p (fun i => truncateTorusHk (Nat.zero_le _) (f i)))) := by
  have htp := (preparation_endpoint hprem hΛ).1
  have he := preparation_path_expansion hprem hq hΛ hζ hchart hmol
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ⟨htp.1.le, htp.2⟩ f u w hs v
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ⟨htp.1.le, le_rfl⟩
  rw [he, pathBlocks_jointOperator]
  exact sub_nested_sum_map (truncateTorusHk (E := h v) (le_max_right Mout (K v)))
    (Finset.range (H + 1))
    (fun n p => incomingTrajectory (n := n) hprem hq hΛ hζ hchart hmol v p f
      (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m))
    (fun n p => truncatedPathResponse (n := n) R v p
      (fun i => truncateTorusHk (Nat.zero_le _) (f i)))

include hprem hq hΛ hζ hchart hmol in
/-- The factorial norm of the total physical error has the positive power-sum majorant. -/
theorem family_path_error_majorant (hCP : 0 ≤ CP) (hA : ∀ v u, 0 ≤ A v u)
    (f : ∀ i, TorusHk (K i) (h i)) (Fv : ι → ℝ)
    (hf : ∀ i, torusHkNorm ρold (le_refl (K i)) (f i) ≤ Fv i)
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionTorus ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
      (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u w) (v : ι) :
    torusHkNorm (ocRhoMol α q Λ m cMol ν) (le_refl (K v))
      (u v (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) - truncateTorusHk (le_max_right Mout (K v))
        (jointOperator K Mout H (pathDiagonalBlock R) (pathSourceBlock R)
          (fun i => truncateTorusHk (Nat.zero_le _) (f i)) v)) ≤
      ∑ z, (CP * ocEpsilon q Λ (m - 1) ^ Pacc) * pathPowerMatrix A H v z * Fv z := by
  rw [family_path_error_sum hprem hq hΛ hζ hchart hmol Mout C CP c Pacc R f u w hs v]
  apply (CycleComparison.Reconstruction.torusHkNorm_sum_le _ _ _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.range (H + 1), ∑ p : Incoming ι n,
        torusHkNorm (ocRhoMol α q Λ m cMol ν) (le_refl (K v))
          (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f
            (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) - truncateTorusHk (le_max_right Mout (K v))
              (truncatedPathResponse R v p (fun i => truncateTorusHk (Nat.zero_le _) (f i)))) :=
      Finset.sum_le_sum (fun n _ => CycleComparison.Reconstruction.torusHkNorm_sum_le _ _ _ _)
    _ ≤ ∑ n ∈ Finset.range (H + 1), ∑ p : Incoming ι n,
        CP * ocEpsilon q Λ (m - 1) ^ Pacc * incomingWeight A v p * Fv (incomingVertices v p 0) := by
      apply Finset.sum_le_sum
      intro n hn
      exact Finset.sum_le_sum (fun p _ => path_error_bound hprem hq hΛ hζ hchart hmol
        Mout C CP c Pacc R hCP hA v p (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) f Fv hf)
    _ = _ := path_weighted_majorant_sum A H v Fv (CP * ocEpsilon q Λ (m - 1) ^ Pacc)

include hprem hq hΛ hζ hchart hmol in
/-- The same path-core operators satisfy the complete original-mass physical error. -/
theorem pathBlocks_error (hCP : 0 ≤ CP) :
    IsJointError π K Mout H D ν tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m)
      (ocRhoMol α q Λ m cMol ν) ρold (ocEpsilon q Λ (m - 1)) Pacc
      (CP * pathErrorFactor Cth H) (streamVel (Φ m))
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (pathDiagonalBlock R) (pathSourceBlock R) := by
  intro f Fv hf u w hs
  have hA (v z : ι) : 0 ≤ A v z := (mul_nonneg_iff_of_pos_left
    (Real.sqrt_pos.mpr (div_pos (hprem.hπ z) (hprem.hπ v)))).mp (hprem.henv.nonneg v z)
  have hE := (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le
  have hprice : 0 ≤ CP * ocEpsilon q Λ (m - 1) ^ Pacc :=
    mul_nonneg hCP (Real.rpow_nonneg hE Pacc)
  have hθ : 0 ≤ pathErrorFactor Cth H := zero_le_one.trans (pathErrorFactor_one_le Cth H)
  have hrow (v : ι) : ∑ z, massConjugatedMatrix π A v z ≤ max Cth 0 + 1 :=
    (hprem.henv.row_sum v).trans (envelope_schur_scale_le Cth Θ hprem.hΘ₀ hprem.hΘ₁)
  have hcol (z : ι) : ∑ v, massConjugatedMatrix π A v z ≤ max Cth 0 + 1 :=
    (hprem.henv.col_sum z).trans (envelope_schur_scale_le Cth Θ hprem.hΘ₀ hprem.hΘ₁)
  let err : ∀ v, TorusHk (K v) (h v) := fun v =>
    u v (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) - truncateTorusHk (le_max_right Mout (K v))
      (jointOperator K Mout H (pathDiagonalBlock R) (pathSourceBlock R)
        (fun i => truncateTorusHk (Nat.zero_le _) (f i)) v)
  have hb := family_path_error_majorant hprem hq hΛ hζ hchart hmol Mout C CP c Pacc R hCP hA f Fv hf u w hs
  have hschur := massScalarSchur π hprem.hπ (pathPowerMatrix A H)
    (pathPowerMatrix_nonneg A hA H) (CP * ocEpsilon q Λ (m - 1) ^ Pacc)
    (pathErrorFactor Cth H) hprice hθ (pathPowerMatrix_row π hprem.hπ A hA Cth H hrow)
    (pathPowerMatrix_col π hprem.hπ A hA Cth H hcol) Fv
    (fun v => torusHkNorm (ocRhoMol α q Λ m cMol ν) (le_refl (K v)) (err v))
    (fun _ => Real.sqrt_nonneg _) hb
  have he : massNormSq (ocRhoMol α q Λ m cMol ν) π (fun v => (err v).val) =
      ∑ v, (π v)⁻¹ * torusHkNorm (ocRhoMol α q Λ m cMol ν) (le_refl (K v)) (err v) ^ 2 := by
    unfold massNormSq
    apply Finset.sum_congr rfl
    intro v _
    rw [torusHkNorm_full, Real.sq_sqrt (factorialNormSq_nonneg _ _)]
  change Real.sqrt (massNormSq (ocRhoMol α q Λ m cMol ν) π (fun v => (err v).val)) ≤ _
  rw [he]
  apply hschur.trans_eq
  ring

end AVRegularity.CycleJointProofs.PathReduction
end
end

section
/-! The raw core yields the exact triangular path reduction ingredient. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs.PathReduction
universe u v w x
namespace AVRegularity.CycleJointProofs.Assembly

/-- Apply the raw core to adapted source chains and assemble the triangular model and error.
The core operators are chosen on their mass-free clauses (`chainCoreChoice`), so the endpoint
and the blocks precede the masses of the family; the clauses for every mass family with the
envelopes follow from the same operators. -/
theorem pathReduction : PathReductionStatement.{u, v, w, x} := by
  intro hcore α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hΛ⟩ := hcore α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛΛ => ?_⟩
  obtain ⟨g₀, hg₀, hP⟩ := hΛ Λ hΛΛ
  refine ⟨g₀, hg₀, fun Pacc hPacc Mout H D Kmax hD => ?_⟩
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, hchart, hmol, hcst⟩ := hP Pacc hPacc Mout H D Kmax hD
  refine ⟨Ks, Ls, Jm, qJ, Jchart, 2, by norm_num, rfl,
    fun Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad hcMol hcOld => ?_⟩
  obtain ⟨C, CP, c, mStar, hc, hC, hCP, hfam⟩ :=
    hcst Ca 1 Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad hcMol hcOld
  refine ⟨C, CP * pathErrorFactor Cth H, c, mStar, hc, hC,
    mul_nonneg hCP (zero_le_one.trans (pathErrorFactor_one_le Cth H)), ?_⟩
  intro ι _ _ h _ _ _ _ _ _ K hK Φ hΦ M' κ hband m hm2 hmStar hmM ν B hν hB hφ
    tS g a B₀ lam l₀ P y₀ cov P' Ctx F hwmeas hprep actual hdepth hdesc htorus hcover hmeas
    A Θ hΘ₀ hΘ₁ htrans hquiet T hTcons hTcov hTq ρold hρold hρrat
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛΛ
  obtain ⟨htpI, htpQ, hquietMargin⟩ :=
    renewal_endpoint_facts (α := α) (q := q) (m := m) ζ hΛ128 ⟨cov.window.1, cov.window.2.1⟩
  refine ⟨((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m,
    chosenDiagonalBlock F actual K Mout A ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) tS
      (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) (ocRhoMol α q Λ m cMol ν) ρold
      (c * Real.sqrt (B * ocTauPP α q Λ m)) Pacc C CP (streamVel (Φ m)),
    chosenSourceBlock F actual K Mout H A ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) tS
      (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) (ocRhoMol α q Λ m cMol ν) ρold
      (c * Real.sqrt (B * ocTauPP α q Λ m)) Pacc C CP (streamVel (Φ m)),
    htpI, htpQ, hquietMargin, fun π hπ henv hpointwise => ?_⟩
  let hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold :=
    ⟨hπ, hK, hΦ, hband, hm2, hmStar, hmM, hν, hB, cov, hwmeas, hprep,
      hdepth, hdesc, htorus, hcover, hmeas, hΘ₀, hΘ₁, henv, hpointwise,
      htrans, hquiet, hTcons, hTcov, hTq, hρold, hρrat⟩
  have hex : ∀ (n : ℕ) (v : ι) (p : Incoming ι n), IncomingValid F A v p → n ≤ H →
      ∃ Tm, ChainCoreProp F actual K Mout A ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) tS
        (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) (ocRhoMol α q Λ m cMol ν) ρold
        (c * Real.sqrt (B * ocTauPP α q Λ m)) Pacc C CP (streamVel (Φ m)) v p Tm := by
    intro n v p hp _hn
    let seq := incomingVertices v p
    have hpos := fun k => (incomingVertices_edges F A v p hp k).2
    have hmass := pathMass_pos seq A hpos
    have hschur := pathMass_schur seq A hpos
    have hpath := pathFamily_jointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold
      hprem seq (pathMass seq A) hmass 1 zero_le_one (le_refl 1) hschur.1 hschur.2
    obtain ⟨Tm, hmodel, hl2, herr⟩ := hfam (pathMass seq A) hpath.hπ (K ∘ seq) hpath.hK
      Φ hpath.hΦ M' κ hpath.hband m hpath.hm2 hpath.hmStar hpath.hmM ν B hpath.hν hpath.hB
      hφ tS g a B₀ lam l₀ P y₀ hpath.cov (F.pathFamily seq) hpath.hwmeas hpath.hprep actual
      hpath.hdepth hpath.hdesc hpath.htorus hpath.hcover hpath.hmeas (pathMatrix seq A) 1
      hpath.hΘ₀ hpath.hΘ₁ hpath.henv hpath.hpointwise hpath.htrans hpath.hquiet
      (ChartedFamily.pathAtlas F seq T) hpath.hTcons hpath.hTcov hpath.hTq ρold hpath.hρold
      hpath.hρrat
    exact ⟨Tm, hmodel, hl2, herr⟩
  let R := chosenCollection F actual K Mout H A ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) tS
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) (ocRhoMol α q Λ m cMol ν) ρold
    (c * Real.sqrt (B * ocTauPP α q Λ m)) Pacc C CP (streamVel (Φ m)) hex
  have hA : ∀ v u, 0 ≤ A v u := fun v u =>
    (mul_nonneg_iff_of_pos_left (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).mp (henv.nonneg v u)
  have hE : 0 ≤ ocEpsilon q Λ (m - 1) := (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)).le
  have hδ : 0 ≤ 1 + CP * ocEpsilon q Λ (m - 1) ^ Pacc :=
    add_nonneg zero_le_one (mul_nonneg hCP (Real.rpow_nonneg hE Pacc))
  have hM := pathBlocks_model R hC hA hδ
  have hJ := pathBlocks_error hprem hq.1 hΛ128 hζ hchart hmol Mout C CP c Pacc R hCP
  have hCPle : CP ≤ CP * pathErrorFactor Cth H :=
    le_mul_of_one_le_right hCP (pathErrorFactor_one_le Cth H)
  have hM' := rawTriangularModel_error_mono F K Mout H A (ocEpsilon q Λ (m - 1)) Pacc
    (c * Real.sqrt (B * ocTauPP α q Λ m)) C CP (CP * pathErrorFactor Cth H) hE hCPle
    (pathDiagonalBlock R) (pathSourceBlock R) hM
  rw [pathDiagonalBlock_chosen, pathSourceBlock_chosen] at hM' hJ
  exact ⟨hM', hJ⟩

end AVRegularity.CycleJointProofs.Assembly
end
end
