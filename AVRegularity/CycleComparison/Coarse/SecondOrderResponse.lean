-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseSlot
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyP
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurMatrix
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurCondition
import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledEnergyTorus
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
import AVRegularity.CoupledEnergy.Variational.DriftCarrierBudget
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleComparison.Coarse

/-! The edge-masked majorant.

`IsCoarseSetting.edge_acyclic : Aedge ^ (H + 1) = 0` cannot hold for an arbitrary positive
majorant `A`. The coarse setting is instantiated with the majorant masked by the edge graph,
`maskedEdgeMatrix adj A v u = if adj v u then A v u else 0`, where `adj v u` says that the
component `u` enters the equation of `v`. If `adj` has depth at most `H` (no chain of `H + 1`
consecutive edges), then the masked matrix is nilpotent of order `H + 1`. Masking only lowers a
nonnegative majorant entrywise, so its row and column sums stay below those of `A`, and the
supplied-mean hypothesis `edge_mean` becomes a masked entrywise (path-product) bound. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The majorant masked by an edge relation. -/
def maskedEdgeMatrix (adj : ι → ι → Prop) [DecidableRel adj] (A : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  Matrix.of fun v u => if adj v u then A v u else 0

variable (adj : ι → ι → Prop) [DecidableRel adj] (A : Matrix ι ι ℝ)

omit [Fintype ι] [DecidableEq ι] in
theorem maskedEdgeMatrix_apply (v u : ι) :
    maskedEdgeMatrix adj A v u = if adj v u then A v u else 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem maskedEdgeMatrix_nonneg (hA : ∀ v u, 0 ≤ A v u) (v u : ι) :
    0 ≤ maskedEdgeMatrix adj A v u := by
  rw [maskedEdgeMatrix_apply]
  split_ifs
  · exact hA v u
  · exact le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem maskedEdgeMatrix_le (hA : ∀ v u, 0 ≤ A v u) (v u : ι) :
    maskedEdgeMatrix adj A v u ≤ A v u := by
  rw [maskedEdgeMatrix_apply]
  split_ifs
  · exact le_rfl
  · exact hA v u

/-- A nonzero entry of a power of the masked matrix is carried by a chain of edges. -/
theorem maskedEdgeMatrix_pow_ne_zero_chain (n : ℕ) (v u : ι)
    (hne : (maskedEdgeMatrix adj A ^ n) v u ≠ 0) :
    ∃ p : Fin (n + 1) → ι, p 0 = v ∧ p (Fin.last n) = u ∧
      ∀ i : Fin n, adj (p i.castSucc) (p i.succ) := by
  induction n generalizing u with
  | zero =>
    refine ⟨fun _ => v, rfl, ?_, fun i => i.elim0⟩
    by_contra hvu
    apply hne
    simp [hvu]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply] at hne
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hw1 : (maskedEdgeMatrix adj A ^ n) v w ≠ 0 := left_ne_zero_of_mul hw
    have hw2 : maskedEdgeMatrix adj A w u ≠ 0 := right_ne_zero_of_mul hw
    have hadj : adj w u := by
      by_contra hn
      apply hw2
      simp [maskedEdgeMatrix_apply, hn]
    obtain ⟨p, hp0, hpn, hp⟩ := ih w hw1
    refine ⟨Fin.snoc p u, ?_, ?_, fun i => ?_⟩
    · rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl, Fin.snoc_castSucc]
      exact hp0
    · simp
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc, show j.castSucc.succ = j.succ.castSucc from rfl,
          Fin.snoc_castSucc]
        exact hp j
      · rw [Fin.snoc_castSucc, show (Fin.last n).succ = Fin.last (n + 1) from rfl, Fin.snoc_last,
          hpn]
        exact hadj

/-- **Nilpotency of the masked majorant.** If every chain of `H + 2` components has a missing
edge, then the masked matrix satisfies `M ^ (H + 1) = 0`. -/
theorem maskedEdgeMatrix_pow_eq_zero (H : ℕ)
    (hdepth : ∀ p : Fin (H + 2) → ι, ∃ k : Fin (H + 1), ¬ adj (p k.castSucc) (p k.succ)) :
    maskedEdgeMatrix adj A ^ (H + 1) = 0 := by
  ext v u
  by_contra hne
  obtain ⟨p, -, -, hp⟩ := maskedEdgeMatrix_pow_ne_zero_chain adj A (H + 1) v u hne
  obtain ⟨k, hk⟩ := hdepth p
  exact hk (hp k)

end AVRegularity.CycleComparison.Coarse
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Coarse

/-! The coarse slot drops leave the derivative reserves for covariance and mean fluxes. -/

theorem coarseSlot_le_input (k J H L N i j : ℕ)
    (hN : N = k + (J + H + 3) * L) : coarseSlot k J H L i j ≤ N := by
  unfold coarseSlot
  rw [hN]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right L (by omega)) k

theorem coarseSlot_diagonal_predecessor (k J H L i j : ℕ)
    (hi : 1 ≤ i) (hiJ : i ≤ J) (hjH : j ≤ H) :
    coarseSlot k J H L (i - 1) j = coarseSlot k J H L i j + L := by
  have he : J + H + 2 - (i - 1) - j = (J + H + 2 - i - j) + 1 := by omega
  unfold coarseSlot
  simp only [he, Nat.add_mul, Nat.one_mul]
  omega

theorem coarseSlot_edge_predecessor (k J H L i j : ℕ)
    (hj : 1 ≤ j) (hiJ : i ≤ J) (hjH : j ≤ H) :
    coarseSlot k J H L i (j - 1) = coarseSlot k J H L i j + L := by
  have he : J + H + 2 - i - (j - 1) = (J + H + 2 - i - j) + 1 := by omega
  unfold coarseSlot
  simp only [he, Nat.add_mul, Nat.one_mul]
  omega

end AVRegularity.CycleComparison.Coarse
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Coarse

/-! The new diagonal primitive is anchored at the incoming time (CC 235, 290). -/

 theorem covarianceMatrix_initial (J : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B t₀ : ℝ) :
    covarianceMatrix J B t₀ t₀ = 0 := by
  ext i j
  simp [covarianceMatrix]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covOperator_zero (φ : Vec 2 → E) : covOperator 0 φ = 0 := by
  funext x
  simp [covOperator]

theorem covOperator_zero_iterate (n : ℕ) (hn : 1 ≤ n) (φ : Vec 2 → E) :
    (covOperator (0 : Matrix (Fin 2) (Fin 2) ℝ))^[n] φ = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Function.iterate_succ_apply']
  exact covOperator_zero _

theorem covPolyP_zero (p : ℕ) (φ : Vec 2 → E) : covPolyP 0 p φ = φ := by
  unfold covPolyP
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n hn hn0
    simp [covOperator_zero_iterate n (by omega) φ]
  · simp

theorem covPolyP_initial (J : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B t₀ : ℝ)
    (p : ℕ) (φ : Vec 2 → E) : covPolyP (covarianceMatrix J B t₀ t₀) p φ = φ := by
  rw [covarianceMatrix_initial, covPolyP_zero]

end AVRegularity.CycleComparison.Coarse
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The zero coupling used by every genuine second-order coarse response. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_zero_coefficient (j : ℕ) (w : DerivativeWord2 j) :
    orderedCoefficientDerivative (0 : Vec 2 → E →L[ℝ] F) j w = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    simp [orderedCoefficientDerivative, ih]

theorem coefficientDerivativeArray_zero_coefficient (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (0 : Vec 2 → E →L[ℝ] F) j x = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply WithLp.ofLp_injective 2
  funext w
  simp [coefficientDerivativeArray_apply, orderedCoefficientDerivative_zero_coefficient]

theorem coefficientSeminorm_zero_coefficient (ρ : ℝ) (K : ℕ) (a b : ℝ) :
    coefficientSeminorm ρ K a b (0 : ℝ → Vec 2 → E →L[ℝ] F) = 0 := by
  simp [coefficientSeminorm, coefficientDerivativeArray_zero_coefficient]

theorem coefficientSeminorm_const_zero (ρ : ℝ) (K : ℕ) (a b : ℝ) :
    coefficientSeminorm ρ K a b (fun (_ : ℝ) (_ : Vec 2) => (0 : E →L[ℝ] F)) = 0 := by
  exact coefficientSeminorm_zero_coefficient ρ K a b

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

omit [Fintype ι] in
theorem schurMatrix_zero_coefficient (ν ρ : ℝ) (π : ι → ℝ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) : schurMatrix (h := h) ν ρ π K D a b (fun _ _ _ _ _ => 0) = 0 := by
  funext i j
  simp [schurMatrix, coefficientSeminorm_const_zero]

theorem zeroCoupling_schur (ν ρ : ℝ) (π : ι → ℝ) (K : ι → ℕ) (D : ℕ) (a b : ℝ) :
    SchurCondition (schurMatrix (h := h) ν ρ π K D a b (fun _ _ _ _ _ => 0)) := by
  rw [schurMatrix_zero_coefficient]
  constructor <;> intro i <;> simp

end AVRegularity.CycleComparison.Coarse
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleComparison.Coarse

/-! Each coarse response uses the coupled energy theorem `coupled_energy_torus` for genuine
second-order energy solutions. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}
  (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)

include P in
theorem secondOrderResponse_exists (K : ℕ) (hKN : K ≤ N)
    (f : ∀ i, TorusHk K (h i))
    (F : ∀ i, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc t₀ t₁))) :
    ∃ (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i)),
      IsCoupledWeakSolutionTorus B t₀ t₁ b 2 (fun _ => K) (fun _ _ _ _ _ => 0)
        f F (fun _ _ => 0) u w := by
  exact (coupled_energy_torus (h := h) t₀ t₁ P.window ρ P.rho_pos B P.B_pos b
    P.drift_bdd P.drift_meas P.drift_smooth P.drift_div P.drift_per
    a B₀ lam P.a_nonneg P.B₀_ge P.lam_pos N P.drift_jets P.drift_scale P.drift_small
    2 (by norm_num) π P.mass_pos (fun _ => K) (fun _ => hKN)
    (fun _ _ _ _ _ => 0) (fun _ _ _ => measurable_const)
    (fun _ _ _ _ _ => contDiff_const) (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ => by simp [coefficientSeminorm_const_zero])
    (zeroCoupling_schur B ρ π (fun _ => K) 2 t₀ t₁)
    f F hF (fun _ _ => 0) (fun _ => timeIntegrable_zero _)).1

end AVRegularity.CycleComparison.Coarse
end
end
