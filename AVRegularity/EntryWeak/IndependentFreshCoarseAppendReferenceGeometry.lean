-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentInverseDataCongruence
import AVRegularity.Proofs.Intermediate.EntryWeak.WeakCellInverse
import Mathlib.Analysis.Real.Pi.Bounds

section
section
/-! The next lift forcing is determined by primitive and predecessor germs on an open slow slice. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ} {U : Set (Vec 2)}

theorem independentLiftASource_slow_slice_congr
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a b : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (Y Z : P)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G G' : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (F F' : ℕ → ℕ → ℝ → Vec 2 → P → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (out : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve 1 (fun t _ W => G t W i j))
    (QG' : ∀ i j, IndependentParameterSourceReserve 1 (fun t _ W => G' t W i j))
    (QF : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ u,
      IndependentParameterSourceReserve (D + 2) (fun t z W => F p q t z W u))
    (QF' : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ u,
      IndependentParameterSourceReserve (D + 2) (fun t z W => F' p q t z W u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve 1 (a v u e γ α))
    (Qb : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve 1 (b v u e γ α))
    (hU : IsOpen U)
    (hG : ∀ i j, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t (_ : Vec 2) W => G t W i j) (fun t _ W => G' t W i j))
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α,
      IndependentSourceSlowSliceEqOn L U Y Z (a v u e γ α) (b v u e γ α))
    (hF : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ u,
      IndependentSourceSlowSliceEqOn L U Y Z
        (fun t z W => F p q t z W u) (fun t z W => F' p q t z W u)) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentLiftASource edge a L A η G v F hh n out)
      (independentLiftASource edge b L A η G' v F' hh n out) := by
  have hp1 : hh < hh ∨ (hh = hh ∧ n - 1 < n) := Or.inr ⟨rfl, by omega⟩
  have h1 := independentNormalizedCellB1Source_slow_slice_congr (H := 0)
    L hL Y Z A η G G' v _ _ QG QG'
    ((QF hh (n - 1) hp1 out).restrictOrder 2 (by omega))
    ((QF' hh (n - 1) hp1 out).restrictOrder 2 (by omega)) hU hG (hF _ _ hp1 out)
  intro t X hX z
  dsimp only [independentLiftASource]
  rw [h1 t X hX z]
  refine congrArg₂ (fun r s : ℝ =>
    independentNormalizedCellB1Source L A η G' v
      (fun t z W => F' hh (n - 1) t z W out) t z (L X + Z) + r - s) ?_ ?_
  · by_cases hn2 : 2 ≤ n
    · rw [ite_eq_left hn2, ite_eq_left hn2]
      have hp2 : hh < hh ∨ (hh = hh ∧ n - 2 < n) := Or.inr ⟨rfl, by omega⟩
      exact independentNormalizedCellB2Source_slow_slice_congr (H := 0)
        L hL Y Z A η G G' _ _ QG QG'
        ((QF hh (n - 2) hp2 out).restrictOrder 2 (by omega))
        ((QF' hh (n - 2) hp2 out).restrictOrder 2 (by omega)) hU hG (hF _ _ hp2 out) t X hX z
    · simp only [ite_eq_right hn2]
  · by_cases hhh : hh = 0
    · simp only [ite_eq_left hhh]
    · rw [ite_eq_right hhh, ite_eq_right hhh]
      apply Finset.sum_congr rfl
      intro j _
      have hp : hh - 1 < hh ∨ (hh - 1 = hh ∧ n - j < n) := Or.inl (by omega)
      exact independentSourceComponentArray_slow_slice_congr (H := 0)
        edge a b L hL Y Z A η _ _
        (fun u => (QF _ _ hp u).restrictOrder (0 + 1 + D) (by omega))
        (fun u => (QF' _ _ hp u).restrictOrder (0 + 1 + D) (by omega))
        Qa Qb hU ha (hF _ _ hp) j out t X hX z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Independent inherited flux production retains exact matrix grades and constituent multiplicities. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem independentSourceFlux_matrix_reserve (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (Lslow : Vec 2 →L[ℝ] P) (hLslow : ‖Lslow‖ ≤ 1) (η : ℝ) (A : Vec 2 →L[ℝ] ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (b L : ℕ) (v w : ι)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + D) (fun t z Y => f t z Y u))
    (Qedge : ∀ u (d : Finset.Icc 2 D) γ, ∀ _hγ : γ ∈ edge v u d, ∀ α,
      IndependentParameterSourceReserve H (a v u d γ α))
    (BE BF : ℝ) (hBE : 0 ≤ BE) (hBF : 0 ≤ BF)
    (hQf : ∀ u r, r ≤ H + D → (Qf u).budget r ≤ finiteMatrixPower M b u w * BF)
    (hQe : ∀ u d γ hγ α r, r ≤ H → (Qedge u d γ hγ α).budget r ≤ M v u * BE)
    (hmap : ∀ u (d : Finset.Icc 2 D) γ, γ ∈ edge v u d → ‖γ.map‖ ≤ 1)
    (hlen : ∀ u (d : Finset.Icc 2 D), (edge v u d).length ≤ L) (k : Fin 2) (j : ℕ) :
    ∃ Q : IndependentParameterSourceReserve H (independentSourceFluxComponentCoefficient edge a Lslow A η f k j v),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M (1 + b) v w *
        normalizedSourceFluxMatrixBudget H D L A η BE BF := by
  let CT := normalizedSourceFluxTermBudget H D A η BE BF
  have hCT : 0 ≤ CT := normalizedSourceFluxTermBudget_nonneg H D A η BE BF hBE hBF
  let F := fun u (d : Finset.Icc 2 D) γ α => independentSourceFluxComponentTerm η A Lslow f u d (a v u d γ α) γ α k j
  choose QT hQT using fun u (d : Finset.Icc 2 D) γ (hγ : γ ∈ edge v u d)
    (α : DerivativeWord2 (d.val - 1)) => independentSourceFluxTerm_uniform_reserve H D d.val
      (Finset.mem_Icc.mp d.property).2 η A f u Lslow hLslow (a v u d γ α) γ α k j (Qedge u d γ hγ α) (Qf u)
      (M v u) (finiteMatrixPower M b u w) BE BF (hM v u)
      (finiteMatrixPower_nonneg M hM b u w) hBE hBF (hmap u d γ hγ)
      (hQe u d γ hγ α) (hQf u)
  let QS := fun u (d : Finset.Icc 2 D) γ hγ =>
    IndependentParameterSourceReserve.fintypeSum H (F u d γ) (QT u d γ hγ)
  let QL := fun u (d : Finset.Icc 2 D) => IndependentParameterSourceReserve.listSum (edge v u d) H
    (fun γ t z Y => ∑ α, F u d γ α t z Y) (QS u d)
  let QD := fun u => IndependentParameterSourceReserve.fintypeSum H
    (fun (d : Finset.Icc 2 D) t z Y => ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum)
    (QL u)
  let S := IndependentParameterSourceReserve.fintypeSum H
    (fun u t z Y => ∑ d : Finset.Icc 2 D, ((edge v u d).map (fun γ => ∑ α, F u d γ α t z Y)).sum)
    QD
  have hs (u : ι) (d : Finset.Icc 2 D) γ hγ (r : ℕ) (hr : r ≤ H) :
      (QS u d γ hγ).budget r ≤ (M v u * finiteMatrixPower M b u w) *
        ((Fintype.card (DerivativeWord2 (d.val - 1)) : ℝ) * CT) := by
    rw [IndependentParameterSourceReserve.fintypeSum_budget]
    have hh := Finset.sum_le_sum (fun α (_ : α ∈ Finset.univ) => hQT u d γ hγ α r hr)
    apply hh.trans_eq
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hl (u : ι) (d : Finset.Icc 2 D) (r : ℕ) (hr : r ≤ H) :
      (QL u d).budget r ≤ (M v u * finiteMatrixPower M b u w) *
        ((L : ℝ) * (Fintype.card (DerivativeWord2 (d.val - 1)) : ℝ) * CT) := by
    have hb := IndependentParameterSourceReserve.listSum_uniform_budget (edge v u d) H
      (fun γ t z Y => ∑ α, F u d γ α t z Y) (QS u d)
      (M v u * finiteMatrixPower M b u w)
      ((Fintype.card (DerivativeWord2 (d.val - 1)) : ℝ) * CT) (hs u d) r hr
    apply hb.trans
    have hpos : 0 ≤ (M v u * finiteMatrixPower M b u w) *
        ((Fintype.card (DerivativeWord2 (d.val - 1)) : ℝ) * CT) :=
      mul_nonneg (mul_nonneg (hM v u) (finiteMatrixPower_nonneg M hM b u w))
        (mul_nonneg (Nat.cast_nonneg _) hCT)
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hlen u d)) hpos).trans_eq (by ring)
  have hd (u : ι) (r : ℕ) (hr : r ≤ H) :
      (QD u).budget r ≤ (M v u * finiteMatrixPower M b u w) *
        normalizedSourceFluxMatrixBudget H D L A η BE BF := by
    rw [IndependentParameterSourceReserve.fintypeSum_budget]
    have hh := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => hl u d r hr)
    apply hh.trans_eq
    unfold normalizedSourceFluxMatrixBudget sourceFluxWordCount
    rw [Nat.cast_sum, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  refine ⟨S, ?_⟩
  intro r hr
  rw [IndependentParameterSourceReserve.fintypeSum_budget]
  have hh := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hd u r hr)
  apply hh.trans_eq
  rw [← Finset.sum_mul]
  have hp := congrFun (congrFun (finiteMatrixPower_succ M b) v) w
  change finiteMatrixPower M (b + 1) v w = ∑ u, M v u * finiteMatrixPower M b u w at hp
  rw [← hp, Nat.add_comm b 1]

end AVRegularity.EntryWeakProofs
end
end

section
/-! All fresh stored children over an empty base are the literal indexed finite weak geometry. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshChildSeq (birthLength : ℕ → ℝ) {n : ℕ} (Y : Vec (4 * n)) (j : ℕ) : ChainChild :=
  if h : j < n then independentFreshChild (fun k : Fin n => birthLength k) ⟨j, h⟩ Y else ⟨0, 0⟩

theorem independentFreshChildSeq_ofFn (birthLength : ℕ → ℝ) {n : ℕ} (Y : Vec (4 * n)) :
    List.ofFn (fun j : Fin n => independentFreshChildSeq birthLength Y j) =
      List.ofFn (fun j : Fin n => independentFreshChild (fun k => birthLength k) j Y) := by
  congr 1
  funext j
  simp only [independentFreshChildSeq, dite_eq_left j.is_lt]

theorem independentFreshChain_eq_indexed {n : ℕ} (A : RealChain) (p : ℕ → ℤ)
    (hchildren : A.children = []) (hslots : A.slots = [p 0])
    (birthLength : ℕ → ℝ) (Y : Vec (4 * n)) :
    independentFreshChain A (fun j : Fin n => p (j + 1)) (fun j => birthLength j) Y =
      (⟨A.baseLevel, List.ofFn (fun j : Fin (n + 1) => p j), A.base,
        List.ofFn (fun j : Fin n => independentFreshChildSeq birthLength Y j)⟩ : RealChain) := by
  rw [independentFreshChildSeq_ofFn]
  have hs : A.slots ++ List.ofFn (fun j : Fin n => p (j + 1)) =
      List.ofFn (fun j : Fin (n + 1) => p j) := by
    rw [hslots, List.ofFn_succ]
    rfl
  unfold independentFreshChain
  rw [hs, hchildren, List.nil_append]

theorem independentFreshChain_geom_eq_indexed {n : ℕ} (D : OCData) (A : RealChain) (p : ℕ → ℤ)
    (hchildren : A.children = []) (hslots : A.slots = [p 0])
    (birthLength : ℕ → ℝ) (Y : Vec (4 * n)) :
    (independentFreshChain A (fun j : Fin n => p (j + 1)) (fun j => birthLength j) Y).geom D =
      finiteWeakChainGeom D A.baseLevel A.base p (independentFreshChildSeq birthLength Y) n := by
  rw [independentFreshChain_eq_indexed A p hchildren hslots birthLength Y]
  exact (finiteWeakChainGeom_eq_chain D A.baseLevel A.base p _ n).symm

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal inherited Taylor derivative copies the full independent source flux coefficient. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D H : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_source_flux_taylor_affine
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (hD : 1 ≤ D)
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α, IndependentParameterSourceReserve H (a v u e γ α))
    (J : Vec 2 →L[ℝ] Vec d) (hJ : ‖J‖ ≤ 1) (offset : Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → Vec d → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + D) (fun t z Y => f t z Y u))
    (k : Fin 2) (j : ℕ) (hj : j ≤ D - 1) (v : ι) (t : ℝ) (z X : Vec 2) :
    (Real.exp (A X))⁻¹ •
      ((((j.factorial : ℝ)⁻¹) • iteratedDeriv j
        (fun ε => sourceFlux (independentConstituentEdgeSlice edge a Qa J offset) η ε t
          (fun X z => Real.exp (A X) • f t z (J X + offset)) k X z) 0) v) =
      independentSourceFluxComponentCoefficient edge a J A η f k j v t z (J X + offset) := by
  let es := independentConstituentEdgeSlice edge a Qa J offset
  let fs := fun t z X => f t z (J X + offset)
  let Qs := fun u => (Qf u).affineSlice J hJ offset
  let Qwhole := jointSourcePiReserve (H + D) (fun u t z X => fs t z X u) Qs
  have he : ((((j.factorial : ℝ)⁻¹) • iteratedDeriv j
      (fun ε => sourceFlux es η ε t (fun X z => Real.exp (A X) • fs t z X) k X z) 0) v) =
      sourceFluxComponentCoefficient es η t (fun X z => Real.exp (A X) • fs t z X) k j v X z := by
    rw [sourceFluxCoefficientArray_normalized es hD η t _
      ((Qwhole.exponentialGoodField A t).mono (by omega)) k j X z]
    exact congrFun (congrFun (sourceFluxCoefficientArray_component_eq es η t _ k j
      (Weighted.isBoxSmooth_of_joint_contDiff _ _ _
        ((Qwhole.exponentialGoodField A t).mono (by omega)).1) v) X) z
  rw [he]
  exact independent_source_flux_affine_slice edge a Qa J hJ offset A η f Qf k j v t z X

end AVRegularity.EntryWeakProofs
end
end

section
/-! Positive lower diagonal fields keep one response factor in the uncentered molecular forcing. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

omit [DecidableEq ι] in
theorem independentDiagonalASource_uniform_response (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (F : ℕ → ℕ → ℝ → Vec 2 → P → ι → ℝ) (n : ℕ) (hn : 2 ≤ n) (out : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (Q1 : IndependentParameterSourceReserve (H + 2) (fun t z Y => F 0 (n - 1) t z Y out))
    (Q2 : IndependentParameterSourceReserve (H + 2) (fun t z Y => F 0 (n - 2) t z Y out))
    (θ BG BV B1 B2 : ℝ) (hθ : 0 ≤ θ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hG : ∀ i j r, r ≤ H + 1 → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H → (Qv i).budget r ≤ BV)
    (hQ1 : ∀ r ≤ H + 2, Q1.budget r ≤ θ * B1)
    (hQ2 : ∀ r ≤ H + 2, Q2.budget r ≤ θ * B2) :
    ∃ Q : IndependentParameterSourceReserve H (independentLiftASource edge a L A η G v F 0 n out),
      ∀ r ≤ H, Q.budget r ≤ θ *
        (normalizedCellB1UniformBudget H A η BG BV B1 + normalizedCellB2UniformBudget H A η BG B2) := by
  let R1 := independentNormalizedCellB1SourceReserve H L hL A η G v _ QG Qv Q1
  let R2 := independentNormalizedCellB2SourceReserve H L hL A η G _ QG Q2
  have he : (fun t z Y => independentNormalizedCellB1Source L A η G v
      (fun t z Y => F 0 (n - 1) t z Y out) t z Y + independentNormalizedCellB2Source L A η G
      (fun t z Y => F 0 (n - 2) t z Y out) t z Y) =
      independentLiftASource edge a L A η G v F 0 n out := by
    funext t z Y
    simp only [independentLiftASource, ite_eq_left hn, ite_true, sub_zero]
  refine ⟨(R1.add R2).congrSource he, ?_⟩
  intro r hr
  rw [IndependentParameterSourceReserve.congrSource_budget]
  change R1.budget r + R2.budget r ≤ _
  exact (add_le_add
    (independentNormalizedCellB1SourceReserve_uniform_budget H L hL A η G v _ QG Qv Q1
      θ BG BV B1 hθ hBG hBV hB1 hG hv hQ1 r hr)
    (independentNormalizedCellB2SourceReserve_uniform_budget H L hL A η G _ QG Q2
      θ BG B2 hθ hBG hB2 hG hQ2 r hr)).trans_eq (mul_add θ _ _).symm

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual centered relative shear cancels its small scale before any independent mixed derivative is estimated. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem weak_centered_relative_shear_joint_jet_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (n : ℕ) (phase V : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun Y : Vec 2 × Vec 2 => θ⁻¹ •
      (D.relDisp m slot u r (Y.1 + θ • Y.2) - D.relDisp m slot u r Y.1)) (phase, V)‖ ≤
      (2 : ℝ) ^ n * (|u - r| * (2 * Real.pi) ^ (n + 2) * ocA D.α D.q D.Λ m) * (‖V‖ + n) := by
  exact independent_scaled_difference_jet_bound (D.relDisp m slot u r) n
    ((relDisp_spatial_smooth D m slot u r).of_le (by simp))
    (|u - r| * (2 * Real.pi) ^ (n + 2) * ocA D.α D.q D.Λ m)
    (fun Y => weak_relative_displacement_menu_jet_bound D hΛ hζ m slot hp u r (n + 1) n (by omega) Y)
    (fun Y => weak_relative_displacement_menu_jet_bound D hΛ hζ m slot hp u r (n + 1) (n + 1) le_rfl Y)
    θ hθ hθ₁ phase V

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every actual finite family has a literal all-children native independent representation. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshBaseChain (A : RealChain) : RealChain :=
  ⟨A.baseLevel, [realChainSlotSeq A 0], A.base, []⟩

def independentFreshActualBirthLength (D : OCData) (A : RealChain) (j : Fin A.children.length) : ℝ :=
  D.eps (A.baseLevel + 1 + j)

def independentFreshActualChainPacking (D : OCData) (A : RealChain) : Vec (4 * A.children.length) :=
  independentFreshChildPacking (independentFreshActualBirthLength D A) (fun j => A.children[j])

theorem independentFreshBaseChain_wellSlotted (A : RealChain) : (independentFreshBaseChain A).WellSlotted := rfl

theorem independentFreshActualChainPacking_center_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (bw : ℝ) (hbw : bw ≤ 1 / 10000) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) (j : Fin A.children.length) :
    ‖independentFreshChildProjection j false (independentFreshActualChainPacking D A)‖ ≤ 1 / 8 :=
  admissible_fresh_packing_center_bound D hΛ A bw hbw j₀ level slot hA j

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual temporal partition preserves a full independent vector reserve at a fixed price of five. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentWeakCutoffPartition (D : OCData) (m : ℕ)
    (f : ℤ → ℝ → Vec 2 → P → Vec 2) (t : ℝ) (z : Vec 2) (Y : P) : Vec 2 :=
  ∑ᶠ slot : ℤ, ocCutoff D.α D.q D.Λ m slot t • f slot t z Y

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem independentWeakCutoffPartition_eq_sum
    (D : OCData) (m : ℕ) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (f : ℤ → ℝ → Vec 2 → P → Vec 2) (t : ℝ) (z : Vec 2) (Y : P) :
    independentWeakCutoffPartition D m f t z Y =
      ∑ slot ∈ weakTransferSlots D m t, ocCutoff D.α D.q D.Λ m slot t • f slot t z Y := by
  apply finsum_eq_sum_of_support_subset
  intro slot hs
  apply weak_cutoff_mem_transferSlots D m t hτ slot
  intro hz
  exact hs (by dsimp only; rw [hz, zero_smul])

def independentWeakCutoffPartitionReserve (D : OCData) (hΛ : 1 ≤ D.Λ) (m H : ℕ)
    (hτ : 0 < ocTau D.α D.q D.Λ m)
    (f : ℤ → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ slot, IndependentParameterSourceReserve H (f slot))
    (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQ : ∀ slot n, n ≤ H → (Q slot).budget n ≤ θ * B) :
    IndependentParameterSourceReserve H (independentWeakCutoffPartition D m f) where
  regular t := by
    have he : (fun X : Vec 2 × P => independentWeakCutoffPartition D m f t X.1 X.2) =
        fun X => ∑ slot ∈ weakTransferSlots D m t,
          ocCutoff D.α D.q D.Λ m slot t • f slot t X.1 X.2 := by
      funext X
      exact independentWeakCutoffPartition_eq_sum D m hτ f t X.1 X.2
    rw [he]
    exact ContDiff.sum (fun slot _ => (Q slot).regular t |>.const_smul _)
  periodic t Y k z := by
    dsimp only
    rw [independentWeakCutoffPartition_eq_sum D m hτ,
      independentWeakCutoffPartition_eq_sum D m hτ]
    exact Finset.sum_congr rfl (fun slot _ => congrArg
      (fun a : Vec 2 => ocCutoff D.α D.q D.Λ m slot t • a) ((Q slot).periodic t Y k z))
  measurable Y := by
    have hm slot : Measurable (fun Z : ℝ × Vec 2 =>
        ocCutoff D.α D.q D.Λ m slot Z.1 • f slot Z.1 Z.2 Y) :=
      ((CycleReference.ocCutoff_contDiff hΛ slot).continuous.measurable.comp measurable_fst).smul
        ((Q slot).measurable Y)
    have he (Z : ℝ × Vec 2) : (∑' slot : ℤ,
        ocCutoff D.α D.q D.Λ m slot Z.1 • f slot Z.1 Z.2 Y) =
        independentWeakCutoffPartition D m f Z.1 Z.2 Y := by
      apply tsum_eq_finsum
      apply (weakTransferSlots D m Z.1).finite_toSet.subset
      intro slot hs
      apply weak_cutoff_mem_transferSlots D m Z.1 hτ slot
      intro hz
      exact hs (by dsimp only; rw [hz, zero_smul])
    have hmeas : Measurable (fun Z : ℝ × Vec 2 => ∑' slot : ℤ,
        ocCutoff D.α D.q D.Λ m slot Z.1 • f slot Z.1 Z.2 Y) := Measurable.tsum hm
    simpa only [he] using hmeas
  budget _ := 5 * (θ * B)
  budget_nonneg _ := mul_nonneg (by norm_num) (mul_nonneg hθ hB)
  derivative_bound n hn t X := by
    have he : (fun Z : Vec 2 × P => independentWeakCutoffPartition D m f t Z.1 Z.2) =
        fun Z => ∑ slot ∈ weakTransferSlots D m t,
          ocCutoff D.α D.q D.Λ m slot t • f slot t Z.1 Z.2 := by
      funext Z
      exact independentWeakCutoffPartition_eq_sum D m hτ f t Z.1 Z.2
    have hreg slot : ContDiff ℝ (n : ℕ∞) (fun Z : Vec 2 × P => f slot t Z.1 Z.2) :=
      ((Q slot).regular t).of_le (by exact_mod_cast hn)
    rw [he]
    apply (CycleJointProofs.finite_jet_finset_sum_norm_le _ _ n
      (fun slot _ => (hreg slot).const_smul _) X).trans
    calc
      _ ≤ ∑ _slot ∈ weakTransferSlots D m t, θ * B := by
        apply Finset.sum_le_sum
        intro slot _
        have hcut : 0 ≤ ocCutoff D.α D.q D.Λ m slot t := Real.smoothTransition.nonneg _
        have hcut1 : ocCutoff D.α D.q D.Λ m slot t ≤ 1 := Real.smoothTransition.le_one _
        rw [iteratedFDeriv_const_smul_apply' (hreg slot).contDiffAt,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg hcut]
        exact (mul_le_mul_of_nonneg_left
          (((Q slot).derivative_bound n hn t X).trans (hQ slot n hn))
          hcut).trans
          (mul_le_of_le_one_left (mul_nonneg hθ hB) hcut1)
      _ = _ := by simp only [Finset.sum_const, weakTransferSlots_card, nsmul_eq_mul, Nat.cast_ofNat]

end AVRegularity.EntryWeakProofs
end
end

section
/-! One finite menu price controls all centered shear jets while retaining the primitive amplitude. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def weakCenteredRelativeShearCost (K : ℕ) (R : ℝ) : ℝ :=
  (2 : ℝ) ^ K * (2 * Real.pi) ^ (K + 2) * (R + K)

theorem weakCenteredRelativeShearCost_nonneg (K : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ weakCenteredRelativeShearCost K R := by
  unfold weakCenteredRelativeShearCost
  positivity

theorem weak_centered_relative_shear_joint_menu_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (K n : ℕ) (hn : n ≤ K)
    (R : ℝ) (phase V : Vec 2) (hV : ‖V‖ ≤ R) :
    ‖iteratedFDeriv ℝ n (fun Y : Vec 2 × Vec 2 => θ⁻¹ •
      (D.relDisp m slot u r (Y.1 + θ • Y.2) - D.relDisp m slot u r Y.1)) (phase, V)‖ ≤
      (|u - r| * ocA D.α D.q D.Λ m) * weakCenteredRelativeShearCost K R := by
  have hA : 0 ≤ ocA D.α D.q D.Λ m :=
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hpow₂ : (2 : ℝ) ^ n ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hn
  have hpowπ : (2 * Real.pi) ^ (n + 2) ≤ (2 * Real.pi) ^ (K + 2) :=
    pow_le_pow_right₀ hpi (by omega)
  have hR : 0 ≤ R := (norm_nonneg V).trans hV
  have hsum : ‖V‖ + (n : ℝ) ≤ R + K := add_le_add hV (by exact_mod_cast hn)
  have hh := weak_centered_relative_shear_joint_jet_bound D hΛ hζ m slot hp u r θ hθ hθ₁ n phase V
  have hinside := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpowπ (abs_nonneg (u - r))) hA
  have hhead := mul_le_mul hpow₂ hinside (by positivity) (by positivity)
  exact hh.trans ((mul_le_mul hhead hsum (by positivity) (by positivity)).trans_eq (by
    unfold weakCenteredRelativeShearCost
    ring))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Independent child centers normalized at their parent's wavelength. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

def independentFreshCoarseBirthLength (D : OCData) (A : RealChain)
    (j : Fin A.children.length) : ℝ := D.eps (A.baseLevel + j)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine independent earlier forcing identifies the literal ordered native mean correction. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D H : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_lift_mean_composition_affine (j : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (f : ℝ → Vec 2 → ι → ℝ) (p q hh : ℕ)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (offset : Vec d) (A : Vec 2 →L[ℝ] ℝ)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ)
    (QF : ∀ u, IndependentParameterSourceReserve (H + j) (fun t z Y => F t z Y u))
    (hA : ∀ t z X u, F t z (L X + offset) u = normalizedLiftASource Q Cc f p q A t z X u)
    (v : ι) (t : ℝ) (z X : Vec 2)
    (hcopy : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      Cc hh j m.val α t X z v u 1 = c m.val α t z (L X + offset) v u) :
    (Real.exp (A X))⁻¹ • liftApply j (Cc hh j) (liftMean Q Cc f p q) t X z v =
      independentLiftMeanCompositionSource j c L A F v t z (L X + offset) := by
  let Qwhole := independentSourcePiReserve (H + j) (fun u t z Y => F t z Y u) QF
  have hmean : liftMean Q Cc f p q =
      fun t X => Real.exp (A X) • (fun u => fieldCellMean (fun z => F t z (L X + offset) u)) := by
    funext t X u
    have hc : Continuous (fun z => F t z (L X + offset)) :=
      ((Qwhole.regular t).comp₂ contDiff_id (contDiff_const (c := L X + offset))).continuous
    have he : (fun z => F t z (L X + offset)) =
        fun z => (Real.exp (A X))⁻¹ • liftA Q Cc f p q t X z := by
      funext z w
      exact hA t z X w
    have hp := fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) u) hc
    change fieldCellMean (fun z => F t z (L X + offset) u) =
      fieldCellMean (fun z => F t z (L X + offset)) u at hp
    rw [Pi.smul_apply, hp, he, fieldCellMean_smul, Pi.smul_apply,
      smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
    rfl
  rw [hmean]
  exact independent_lift_apply_affine_slice j c (Cc hh j) L hL offset A
    (fun t Y u => fieldCellMean (fun z => F t z Y u))
    (fun u => (QF u).mean) v t z X hcopy

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! The literal odd/scheduled proof-indexed temporal sum preserves produced reserves. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independentWeakConditionalPartitionReserve
    (D : OCData) (hΛ : 1 ≤ D.Λ) (m H : ℕ) (hτ : 0 < ocTau D.α D.q D.Λ m)
    (Eligible : ℤ → Prop)
    (f : ∀ slot, Eligible slot → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ slot h, IndependentParameterSourceReserve H (f slot h))
    (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQ : ∀ slot h n, n ≤ H → (Q slot h).budget n ≤ θ * B) :
    ∃ R : IndependentParameterSourceReserve H
      (independentWeakCutoffPartition D m (fun slot t z Y => ∑ᶠ h : Eligible slot, f slot h t z Y)),
      ∀ n ≤ H, R.budget n ≤ θ * (5 * B) := by
  classical
  let g := fun slot t z Y => ∑ᶠ h : Eligible slot, f slot h t z Y
  have hs slot : ∃ R : IndependentParameterSourceReserve H (g slot),
      ∀ n ≤ H, R.budget n ≤ θ * B := by
    by_cases he : Eligible slot
    · have hh : f slot he = g slot := by
        funext t z Y
        exact (finsum_eq_single (fun h : Eligible slot => f slot h t z Y) he
          (fun h hh => False.elim (hh (Subsingleton.elim h he)))).symm
      refine ⟨(Q slot he).congrSource hh, ?_⟩
      intro n hn
      rw [IndependentParameterSourceReserve.congrSource_budget]
      exact hQ slot he n hn
    · have : IsEmpty (Eligible slot) := ⟨he⟩
      have hh : (fun (_t : ℝ) (_z : Vec 2) (_Y : P) => (0 : Vec 2)) = g slot := by
        funext t z Y
        exact (finsum_of_isEmpty _).symm
      refine ⟨(IndependentParameterSourceReserve.zero H).congrSource hh, ?_⟩
      intro n _
      rw [IndependentParameterSourceReserve.congrSource_budget]
      exact mul_nonneg hθ hB
  choose R hR using hs
  refine ⟨independentWeakCutoffPartitionReserve D hΛ m H hτ g R θ B hθ hB hR, ?_⟩
  intro n _
  change 5 * (θ * B) ≤ θ * (5 * B)
  exact le_of_eq (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.EntryWeakProofs

example (l sZ : ℕ) (hl : sZ + 2 ≤ l) (hl₃ : 3 ≤ l) (CG Cv ω : ℝ) (hω₀ : 0 < ω)
    (hω : ω < 3 * Real.pi ^ 2 / 2) :
    ∃ Pe₀ C : ℝ, 0 < Pe₀ ∧ 0 < C ∧
    ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (Pe t₀ t₁ : ℝ),
      t₀ ≤ t₁ → 0 ≤ Pe → Pe ≤ Pe₀ →
      (∀ i j, Measurable fun t' => G t' i j) →
      (∀ t (k : Vec 2), 3 / 4 * ∑ i, k i ^ 2 ≤ ∑ i, ∑ j, G t i j * k i * k j) →
      (∀ t i j, |G t i j| ≤ CG) →
      Measurable (fun p : ℝ × Vec 2 => v p.1 p.2) →
      (∀ t, ContDiff ℝ ((l + 1 : ℕ) : ℕ∞) (v t)) →
      (∀ t, AVenhance.IsZ2Periodic (v t)) →
      (∀ t (j : ℕ), j ≤ l + 1 → ∀ z, ‖iteratedFDeriv ℝ j (v t) z‖ ≤ Cv) →
      (∀ t z, ∑ i : Fin 2, fderiv ℝ (fun z' => v t z' i) z (Pi.single i 1) = 0) →
    ∀ (c₀ : Vec 2 → ℝ) (g : ℝ → Vec 2 → ℝ) (Ng : ℝ),
      ContDiff ℝ (l : ℕ∞) c₀ → AVenhance.IsZ2Periodic c₀ → (∫ z in AVenhance.unitCube, c₀ z = 0) →
      Measurable (fun p : ℝ × Vec 2 => g p.1 p.2) →
      (∀ t, ContDiff ℝ (l : ℕ∞) (g t)) → (∀ t, AVenhance.IsZ2Periodic (g t)) →
      (∀ t (j : ℕ), j ≤ l → ∀ z, ‖iteratedFDeriv ℝ j (g t) z‖ ≤ Ng) →
      (∀ t, ∫ z in AVenhance.unitCube, g t z = 0) →
      (∃ c : ℝ → Vec 2 → ℝ, IsCellFieldInverse G (fun t z => Pe • v t z) sZ t₀ t₁ c₀ g c) ∧
      (∀ c c' : ℝ → Vec 2 → ℝ,
        IsCellFieldInverse G (fun t z => Pe • v t z) sZ t₀ t₁ c₀ g c →
        IsCellFieldInverse G (fun t z => Pe • v t z) sZ t₀ t₁ c₀ g c' →
        ∀ t ∈ Set.Icc t₀ t₁, c t =ᵐ[volume.restrict AVenhance.unitCube] c' t) ∧
      ∀ c : ℝ → Vec 2 → ℝ,
        IsCellFieldInverse G (fun t z => Pe • v t z) sZ t₀ t₁ c₀ (fun _ _ => 0) c →
        ∀ t ∈ Set.Icc t₀ t₁,
          ∫ z in AVenhance.unitCube, c t z ^ 2 ≤
            C ^ 2 * Real.exp (-(2 * ω * (t - t₀))) * ∫ z in AVenhance.unitCube, c₀ z ^ 2 :=
  AVRegularity.Providers.weak_cell_inverse l sZ hl hl₃ CG Cv ω hω₀ hω

end AVRegularity.EntryWeakProofs

end
end

section
/-! Parent-normalized coordinates reconstruct every literal child family. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshCoarseChainPacking (D : OCData) (A : RealChain) : Vec (4 * A.children.length) :=
  independentFreshChildPacking (independentFreshCoarseBirthLength D A) (fun j => A.children[j])

theorem independentFreshCoarseChainPacking_reconstruct (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (hA : A.WellSlotted) :
    independentFreshChain (independentFreshBaseChain A)
      (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) (independentFreshCoarseBirthLength D A)
      (independentFreshCoarseChainPacking D A) = A := by
  unfold independentFreshCoarseChainPacking
  have hb : ∀ j, independentFreshCoarseBirthLength D A j ≠ 0 :=
    fun j => (show 0 < D.eps (A.baseLevel + j) from Construction.Stream.ocEpsilon_pos hΛ).ne'
  rw [independentFreshChain_reconstruct (independentFreshBaseChain A)
    (fun j : Fin A.children.length => realChainSlotSeq A (j + 1))
    (independentFreshCoarseBirthLength D A) hb (fun j => A.children[j])]
  have hs : [realChainSlotSeq A 0] ++ List.ofFn (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) = A.slots := by
    rw [← realChain_slots_ofFn A hA, List.ofFn_succ]
    rfl
  change (⟨A.baseLevel, [realChainSlotSeq A 0] ++ List.ofFn (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)),
    A.base, [] ++ List.ofFn (fun j : Fin A.children.length => A.children[j])⟩ : RealChain) = A
  rw [hs, List.nil_append]
  have hc : List.ofFn (fun j : Fin A.children.length => A.children[j]) = A.children :=
    List.ofFn_get A.children
  rw [hc]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual centered shear transitions retain uniform full phase/displacement jets. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def weakCenteredShearTransition (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ)
    (Y : Vec 2 × Vec 2) : Vec 2 :=
  Y.2 + D.relDisp m slot u r (Y.1 + Y.2) - D.relDisp m slot u r Y.1

theorem weakCenteredShearTransition_contDiff (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (weakCenteredShearTransition D m slot u r) :=
  (contDiff_snd.add ((relDisp_spatial_smooth D m slot u r).comp
    (contDiff_fst.add contDiff_snd))).sub ((relDisp_spatial_smooth D m slot u r).comp contDiff_fst)

theorem weak_centered_shear_transition_positive_jet_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (R : ℝ)
    (phase V : Vec 2) (hV : ‖V‖ ≤ R) :
    ‖iteratedFDeriv ℝ n (weakCenteredShearTransition D m slot u r) (phase, V)‖ ≤
      1 + weakCenteredRelativeShearCost K R := by
  let P : (Vec 2 × Vec 2) →L[ℝ] Vec 2 := ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2)
  let δ : Vec 2 × Vec 2 → Vec 2 := fun Y =>
    D.relDisp m slot u r (Y.1 + Y.2) - D.relDisp m slot u r Y.1
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Y => by
    rw [one_mul]; exact norm_snd_le Y)
  have hδ : ContDiff ℝ (⊤ : ℕ∞) δ :=
    ((relDisp_spatial_smooth D m slot u r).comp (contDiff_fst.add contDiff_snd)).sub
      ((relDisp_spatial_smooth D m slot u r).comp contDiff_fst)
  have hd := weak_centered_relative_shear_joint_menu_bound D hΛ hζ m slot hp u r 1
    (by norm_num) (by norm_num) K n hnK R phase V hV
  simp only [inv_one, one_smul] at hd
  have hcost := weakCenteredRelativeShearCost_nonneg K R ((norm_nonneg V).trans hV)
  have he : weakCenteredShearTransition D m slot u r = P + δ := by
    funext Y
    change Y.2 + D.relDisp m slot u r (Y.1 + Y.2) - D.relDisp m slot u r Y.1 =
      Y.2 + (D.relDisp m slot u r (Y.1 + Y.2) - D.relDisp m slot u r Y.1)
    abel
  have hPn : ContDiff ℝ (n : ℕ∞) P := P.contDiff
  have hδn : ContDiff ℝ (n : ℕ∞) δ := hδ.of_le (by simp)
  rw [he, iteratedFDeriv_add_apply hPn.contDiffAt hδn.contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add
    ((linear_positive_derivative_norm_le P n hn _).trans hP)
    (hd.trans ((mul_le_mul_of_nonneg_right hsmall hcost).trans_eq (one_mul _))))

theorem weak_centered_shear_transition_value_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1) (phase V : Vec 2) :
    ‖weakCenteredShearTransition D m slot u r (phase, V)‖ ≤
      (1 + (2 * Real.pi) ^ 2) * ‖V‖ := by
  have hd := weak_centered_relative_shear_joint_menu_bound D hΛ hζ m slot hp u r 1
    (by norm_num) (by norm_num) 0 0 (by omega) ‖V‖ phase V (le_refl _)
  simp only [inv_one, one_smul, norm_iteratedFDeriv_zero, weakCenteredRelativeShearCost,
    pow_zero, one_mul, Nat.zero_add, Nat.cast_zero, add_zero] at hd
  have hδ : ‖D.relDisp m slot u r (phase + V) - D.relDisp m slot u r phase‖ ≤
      (2 * Real.pi) ^ 2 * ‖V‖ :=
    hd.trans ((mul_le_mul_of_nonneg_right hsmall (by positivity)).trans_eq (one_mul _))
  change ‖V + D.relDisp m slot u r (phase + V) - D.relDisp m slot u r phase‖ ≤ _
  rw [add_sub_assoc]
  calc
    _ ≤ ‖V‖ + ‖D.relDisp m slot u r (phase + V) - D.relDisp m slot u r phase‖ := norm_add_le _ _
    _ ≤ ‖V‖ + (2 * Real.pi) ^ 2 * ‖V‖ := add_le_add (le_refl _) hδ
    _ = (1 + (2 * Real.pi) ^ 2) * ‖V‖ := by ring

end AVRegularity.EntryWeakProofs
end
end

section
/-! The independent outer source divergence retains its literal composed matrix grade. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem independentSourceArray_matrix_reserve (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (Lslow : Vec 2 →L[ℝ] P) (hLslow : ‖Lslow‖ ≤ 1) (η : ℝ) (A : Vec 2 →L[ℝ] ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (b L : ℕ) (v w : ι)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + 1 + D) (fun t z Y => f t z Y u))
    (Qedge : ∀ u (d : Finset.Icc 2 D) γ, ∀ _hγ : γ ∈ edge v u d, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u d γ α))
    (BE BF : ℝ) (hBE : 0 ≤ BE) (hBF : 0 ≤ BF)
    (hQf : ∀ u r, r ≤ H + 1 + D → (Qf u).budget r ≤ finiteMatrixPower M b u w * BF)
    (hQe : ∀ u d γ hγ α r, r ≤ H + 1 → (Qedge u d γ hγ α).budget r ≤ M v u * BE)
    (hmap : ∀ u (d : Finset.Icc 2 D) γ, γ ∈ edge v u d → ‖γ.map‖ ≤ 1)
    (hlen : ∀ u (d : Finset.Icc 2 D), (edge v u d).length ≤ L) (j : ℕ) :
    ∃ Q : IndependentParameterSourceReserve H (independentSourceComponentArray edge a Lslow A η f j v),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M (1 + b) v w *
        normalizedSourceArrayMatrixBudget H D L A η BE BF := by
  let F := fun (k : Fin 2) i => independentSourceFluxComponentCoefficient edge a Lslow A η f k i v
  let θ := finiteMatrixPower M (1 + b) v w
  let B := normalizedSourceFluxMatrixBudget (H + 1) D L A η BE BF
  have hθ : 0 ≤ θ := finiteMatrixPower_nonneg M hM (1 + b) v w
  have hB : 0 ≤ B := normalizedSourceFluxMatrixBudget_nonneg _ _ _ _ _ _ _ hBE hBF
  choose QP hQP using fun (k : Fin 2) i => independentSourceFlux_matrix_reserve (H + 1)
    edge a Lslow hLslow η A f M hM b L v w Qf Qedge BE BF hBE hBF hQf hQe hmap hlen k i
  let QS := fun k : Fin 2 => independentCovariantStepReserve H Lslow hLslow A η (F k) k j (QP k)
  have hQS (k : Fin 2) (r : ℕ) (hr : r ≤ H) := independentCovariantStepReserve_uniform_budget
    H Lslow hLslow A η (F k) k j (QP k) θ B hθ hB (hQP k) r hr
  let S := IndependentParameterSourceReserve.fintypeSum H
    (fun k => independentCovariantCoefficientStep Lslow A η k (F k) j) QS
  refine ⟨S, ?_⟩
  intro r hr
  rw [IndependentParameterSourceReserve.fintypeSum_budget]
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hQS k r hr)
  apply hh.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold normalizedSourceArrayMatrixBudget
  dsimp only [θ, B, sourceCovariantWordConstant]
  ring

end AVRegularity.EntryWeakProofs
end
end

section
/-! The admissible zero-child anchor extends exactly the original scheduling sequence. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem weakZeroChildAnchor_slotSeq_prefix (A : RealChain) (hA : A.WellSlotted)
    (slot : ℤ) (n : ℕ) (hn : n ≤ A.children.length) :
    realChainSlotSeq (weakZeroChildAnchor A slot) n = realChainSlotSeq A n := by
  exact List.getD_append A.slots [slot] 0 n (by change A.slots.length = _ at hA; omega)

theorem weakZeroChildAnchor_slotSeq_last (A : RealChain) (hA : A.WellSlotted) (slot : ℤ) :
    realChainSlotSeq (weakZeroChildAnchor A slot) (A.children.length + 1) = slot := by
  change (A.slots ++ [slot]).getD (A.children.length + 1) 0 = slot
  change A.slots.length = A.children.length + 1 at hA
  rw [← hA, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

theorem weakZeroChildAnchor_baseChain (A : RealChain) (hA : A.WellSlotted) (slot : ℤ) :
    independentFreshBaseChain (weakZeroChildAnchor A slot) = independentFreshBaseChain A := by
  change (⟨A.baseLevel, [realChainSlotSeq (weakZeroChildAnchor A slot) 0], A.base, []⟩ : RealChain) = _
  rw [weakZeroChildAnchor_slotSeq_prefix A hA slot 0 (Nat.zero_le _)]
  rfl

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full parent slow coordinates enter the appended center at parent normalization. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshCoarseAppendPacking (r : ℕ) (D : OCData) (m : ℕ)
    (parentSlot slot : ℤ) (θ t : ℝ) (Y : Vec 2 × Vec (2 + 4 * r)) :
    Vec (4 * (r + 1)) :=
  let δ := D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t Y.1
  independentFreshInsertCoordinates r
    (independentStoredParameterProjection (4 * r) Y.2,
      independentIntrinsicSlowProjection (4 * r) Y.2 + θ • δ, Y.1 + δ)

theorem independentFreshCoarseAppendPacking_contDiff (r : ℕ) (D : OCData) (m : ℕ)
    (parentSlot slot : ℤ) (θ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentFreshCoarseAppendPacking r D m parentSlot slot θ t) := by
  have hδ : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 × Vec (2 + 4 * r) =>
      D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t Y.1) :=
    (relDisp_spatial_smooth D m parentSlot _ t).comp contDiff_fst
  have hP := (independentStoredParameterProjection (4 * r)).contDiff.comp
    (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 × Vec (2 + 4 * r) => Y.2))
  have hX := (independentIntrinsicSlowProjection (4 * r)).contDiff.comp
    (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 × Vec (2 + 4 * r) => Y.2))
  exact (independentFreshInsertCoordinates r).contDiff.comp
    (hP.prodMk ((hX.add (hδ.const_smul θ)).prodMk (contDiff_fst.add hδ)))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine lower coefficient fields produce the ordered forcing for every finite exponential test. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def independentLiftCoefficientASource
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (hh n : ℕ) (out inp : ι) : ℝ → Vec 2 → P → ℝ :=
  independentLiftASource edge a L A η G v
    (fun p q t z Y w => independentScalarLiftTestSource q (c p q) A w inp t z Y) hh n out

def independentLiftAFromEarlierCoefficients (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u d γ α)) :
    IndependentParameterSourceReserve H
      (independentLiftCoefficientASource edge a L A η G v c hh n out inp) := by
  let F := fun p q t z Y w => independentScalarLiftTestSource q (c p q) A w inp t z Y
  let Qt := fun p q (hpq : p < hh ∨ (p = hh ∧ q < n)) K (hK : K ≤ H + D + 2) w =>
    independentScalarLiftTestSourceReserve K q (c p q) A w inp
      (fun m α => (Qc p q hpq m α w inp).restrictOrder K hK)
  exact independentLiftASourceReserve H edge a L hL A η G v F hh n out QG Qv
    (Qt hh (n - 1) (Or.inr ⟨rfl, by omega⟩) (H + 2) (by omega) out)
    (fun _ => Qt hh (n - 2) (Or.inr ⟨rfl, by omega⟩) (H + 2) (by omega) out)
    (fun hhh j _ w => Qt (hh - 1) (n - j) (Or.inl (by omega)) (H + 1 + D) (by omega) w) Qa

end AVRegularity.EntryWeakProofs
end
end

section
/-! Reference child coordinates remain inside the unit cutoff without an admissibility assertion. -/
@[expose] public noncomputable section
open Homogenization Filter Topology
namespace AVRegularity.EntryWeakProofs

theorem independentFreshInsertedCarrier_bound (r : ℕ) (P : Vec (4 * r))
    (center phase slow : Vec 2) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ B)
    (hcenter : ‖center‖ ≤ B) (hslow : ‖slow‖ ≤ B) :
    ‖independentFreshCarrierCoordinates (r + 1)
      (independentIntrinsicParameterPacking (4 * (r + 1)) slow
        (independentFreshInsertCoordinates r (P, center, phase)))‖ ≤ B := by
  apply independentFreshCarrierCoordinates_norm_le_of_bounds _ _ B hB
  · intro j
    rw [independentIntrinsicParameterPacking_stored]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [independentFreshInsertCoordinates_last_center]
      exact hcenter
    · rw [← independentFreshPrefixProjection_component,
        independentFreshInsertCoordinates_prefix]
      exact hc i
  · rw [independentIntrinsicParameterPacking_slow]
    exact hslow

end AVRegularity.EntryWeakProofs
end
end

section
/-! Adding an independent slow coordinate does not introduce an inverse wavelength price. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coarse_append_positive_jet_bound (r n : ℕ) (hn : 1 ≤ n)
    (P : E →L[ℝ] Vec (4 * r)) (S F : E →L[ℝ] Vec 2)
    (hP : ‖P‖ ≤ 1) (hS : ‖S‖ ≤ 1) (hF : ‖F‖ ≤ 1)
    (δ : E → Vec 2) (hδ : ContDiff ℝ (n : ℕ∞) δ)
    (θ B : ℝ) (hθ : |θ| ≤ 1) (x : E)
    (hb : ‖iteratedFDeriv ℝ n δ x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => independentFreshInsertCoordinates r
      (P y, S y + θ • δ y, F y + δ y)) x‖ ≤ 1 + B := by
  let T : Vec 2 →L[ℝ] Vec 2 := θ • ContinuousLinearMap.id ℝ (Vec 2)
  have hT : ‖T‖ ≤ 1 := by
    change ‖θ • ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
    exact hθ
  have hscaled : ‖iteratedFDeriv ℝ n (fun y => θ • δ y) x‖ ≤ B := by
    have hh := T.norm_iteratedFDeriv_comp_left hδ.contDiffAt (n := n) (le_refl _) (x := x)
    exact hh.trans (((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans_eq
      (one_mul _)).trans hb)
  have hPn : ‖iteratedFDeriv ℝ n P x‖ ≤ 1 :=
    (linear_positive_derivative_norm_le P n hn x).trans hP
  have hSn : ‖iteratedFDeriv ℝ n S x‖ ≤ 1 :=
    (linear_positive_derivative_norm_le S n hn x).trans hS
  have hFn : ‖iteratedFDeriv ℝ n F x‖ ≤ 1 :=
    (linear_positive_derivative_norm_le F n hn x).trans hF
  have hcenter : ‖iteratedFDeriv ℝ n (fun y => S y + θ • δ y) x‖ ≤ 1 + B :=
    (CycleJointProofs.finite_jet_add_norm_le S (fun y => θ • δ y) n
      S.contDiff (hδ.const_smul θ) x).trans (add_le_add hSn hscaled)
  have hphase : ‖iteratedFDeriv ℝ n (fun y => F y + δ y) x‖ ≤ 1 + B :=
    (CycleJointProofs.finite_jet_add_norm_le F δ n F.contDiff hδ x).trans
      (add_le_add hFn hb)
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  let V := fun y => (P y, S y + θ • δ y, F y + δ y)
  have hV : ContDiff ℝ (n : ℕ∞) V :=
    P.contDiff.prodMk ((S.contDiff.add (hδ.const_smul θ)).prodMk (F.contDiff.add hδ))
  have hi := independent_joint_pair_jet_bound (fun y => S y + θ • δ y)
    (fun y => F y + δ y) n (S.contDiff.add (hδ.const_smul θ)) (F.contDiff.add hδ) x
  have ho := independent_joint_pair_jet_bound P
    (fun y => (S y + θ • δ y, F y + δ y)) n P.contDiff
    ((S.contDiff.add (hδ.const_smul θ)).prodMk (F.contDiff.add hδ)) x
  have hVn : ‖iteratedFDeriv ℝ n V x‖ ≤ 1 + B :=
    ho.trans (max_le (hPn.trans (le_add_of_nonneg_right hB))
      (hi.trans (max_le hcenter hphase)))
  have hh := (independentFreshInsertCoordinates r).norm_iteratedFDeriv_comp_left
    hV.contDiffAt (n := n) (le_refl _) (x := x)
  exact hh.trans (((mul_le_mul_of_nonneg_right (independentFreshInsertCoordinates_norm_le r)
    (norm_nonneg _)).trans_eq (one_mul _)).trans hVn)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual moving reference sampling stays in the fixed inner strip needed by the next depth. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseAppendPacking_carrier_bound (r : ℕ)
    (D : OCData) (m : ℕ) (parentSlot slot : ℤ) (ell : ℝ) (hell : |ell| ≤ 1)
    (t : ℝ) (z : Vec 2) (Y : Vec (2 + 4 * r))
    (hc : ∀ j, ‖independentFreshChildProjection j false
      (independentStoredParameterProjection (4 * r) Y)‖ ≤ 3 / 16)
    (hY : ‖independentIntrinsicSlowProjection (4 * r) Y‖ ≤ 1 / 8)
    (hδ : ‖D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t z‖ ≤ 1 / 16) :
    ‖independentFreshCarrierCoordinates (r + 1)
      (independentIntrinsicParameterPacking (4 * (r + 1)) 0
        (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y)))‖ ≤ 3 / 16 := by
  dsimp only [independentFreshCoarseAppendPacking]
  apply independentFreshInsertedCarrier_bound r _ _ _ _ (3 / 16) (by norm_num) hc ?_ ?_
  · have hs : ‖ell • D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t z‖ ≤ 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) hell).trans hδ
    exact (norm_add_le _ _).trans ((add_le_add hY hs).trans_eq (by norm_num))
  · simp only [norm_zero]
    norm_num

end AVRegularity.EntryWeakProofs
end
end

section
/-! The full coarse sampling map realizes the true appended recentered family's geometry. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseAppendPacking_reference_geom {r : ℕ} (D : OCData)
    (A : RealChain) (hA : A.WellSlotted) (slots : Fin (r + 1) → ℤ)
    (birthLength : Fin (r + 1) → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hbirth : birthLength (Fin.last r) = ρ) (t : ℝ)
    (Y : Vec 2 × Vec (2 + 4 * r)) :
    let P := independentStoredParameterProjection (4 * r) Y.2
    let B := independentFreshChain A (fun j => slots j.castSucc)
      (fun j => birthLength j.castSucc) P
    (independentFreshChain A slots birthLength
      (independentFreshCoarseAppendPacking r D (A.ctxLevel + r) B.slot (slots (Fin.last r))
        (D.eps (A.ctxLevel + r) / ρ) t Y)).geom D =
      (((B.recenter D (ρ • independentIntrinsicSlowProjection (4 * r) Y.2)).appendChild D
        (slots (Fin.last r)) t Y.1).geom D) := by
  dsimp only
  let B := independentFreshChain A (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) (independentStoredParameterProjection (4 * r) Y.2)
  have hB : B.WellSlotted := independentFreshChain_wellSlotted A hA _ _ _
  have hctx : B.ctxLevel = A.ctxLevel + r := independentFreshChain_ctxLevel A _ _ _
  rw [independentFreshChain_geom_succ D A hA]
  simp only [independentFreshCoarseAppendPacking, independentFreshInsertCoordinates_prefix,
    independentFreshChild, independentFreshInsertCoordinates_last_center,
    independentFreshInsertCoordinates_last_phase, hbirth]
  rw [weak_appendChild_recenter_coarse_reference_geom D B hB _ _ _ _ ρ hρ, hctx]

end AVRegularity.EntryWeakProofs
end
end
end
