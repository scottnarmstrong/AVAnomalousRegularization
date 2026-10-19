-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovarianceFluxRegLiftFlux
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Mean
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import AVRegularity.Definitions.Construction.ResidualOps
public import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
public import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Smooth
import Mathlib.Combinatorics.SimpleGraph.Basic

section
/-! The diagonal candidate of the Hilbert lift at grade zero, and the algebraic clauses of
the lift relation for it.

At grade zero the lift equations contain no source edge, so the Hilbert lift is the scalar lift on
each component: `C'_{vu} = δ_{vu} C0 · id`. `hlDiagCoeff c` is this array. -/

/-! Transfer of the grade-zero recursion from the diagonal Hilbert candidate to the scalar lift.

Fix a component `v` and a functional `ℓ` of its space. The scalarization `hlScal ℓ v a` of a Hilbert
field `a` is the scalar field `ℓ (a · v)`. For the diagonal candidate, `ℓ` of the `v` component of
`liftApply`, `liftA`, `liftMean`, `liftCellSource` is the same operator of the scalar lift applied to
the scalarization, as long as the fields are smooth enough for `fderiv` to commute with `ℓ`. -/

@[expose] public noncomputable section

namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLZero

section
open Homogenization AVRegularity.Sobolev AVRegularity

variable {ι : Type*} [DecidableEq ι] {hs : ι → Type*}
  [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)]

/-- The identity from the `u` component to the `v` component when `u = v`, zero otherwise. -/
def hlDiagMap (hs : ι → Type*) [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)]
    (v u : ι) : hs u →L[ℝ] hs v :=
  if h : u = v then (by subst h; exact ContinuousLinearMap.id ℝ (hs u)) else 0

theorem hlDiagMap_self (v : ι) : hlDiagMap hs v v = ContinuousLinearMap.id ℝ (hs v) := by
  simp [hlDiagMap]

theorem hlDiagMap_ne {v u : ι} (h : v ≠ u) : hlDiagMap hs v u = 0 := by
  simp [hlDiagMap, Ne.symm h]

/-- The diagonal candidate: grade zero only, `δ_{vu} (C0 0 n m α t X z 0 0) 1 · id`. -/
def hlDiagCoeff (hs : ι → Type*) [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)]
    (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ)) : ℕ → ℕ → LiftCoeff ι hs :=
  fun hh n m α t X z v u => if hh = 0 then (c 0 n m α t X z 0 0 1) • hlDiagMap hs v u else 0

theorem hlDiagCoeff_apply_zero (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ)) (n m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    hlDiagCoeff hs c 0 n m α t X z v u = (c 0 n m α t X z 0 0 1) • hlDiagMap hs v u := by
  simp [hlDiagCoeff]

/-- The `v` component of `liftApply` of the diagonal candidate. -/
theorem liftApply_hlDiag [Fintype ι] (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ)) (n : ℕ)
    (a : ℝ → Vec 2 → ∀ i, hs i) (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n (hlDiagCoeff hs c 0 n) a t X z v =
      ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
        (c 0 n m α t X z 0 0 1) • orderedDerivative α (a t) X v := by
  unfold liftApply
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_eq_single v]
  · rw [hlDiagCoeff_apply_zero, hlDiagMap_self]; rfl
  · intro u _ hu
    rw [hlDiagCoeff_apply_zero, hlDiagMap_ne (Ne.symm hu)]; simp
  · intro h; exact absurd (Finset.mem_univ v) h

/-- The scalar `liftApply` on the one-point family. -/
theorem liftApply_scalar_fin1 (c : LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ)) (n : ℕ)
    (b : ℝ → Vec 2 → Fin 1 → ℝ) (t : ℝ) (X z : Vec 2) :
    liftApply n c b t X z 0 =
      ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
        (c m α t X z 0 0 1) * orderedDerivative α (b t) X 0 := by
  unfold liftApply
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
  rw [Fintype.sum_unique]
  have key : ∀ (l : ℝ →L[ℝ] ℝ) (x : ℝ), l x = l 1 * x := fun l x => by
    conv_lhs => rw [show x = x • (1 : ℝ) by simp]
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [key]
  rfl

theorem orderedDerivative_word_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : DerivativeWord2 0) (g : Vec 2 → E) : orderedDerivative α g = g := by
  simp [orderedDerivative]

/-- Clause 1 (the zero-degree array is the identity). -/
theorem hlDiag_clause_one [Fintype ι] (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    {t₀ t₁ : ℝ}
    (h0 : ∀ a₀ : Vec 2 → Fin 1 → ℝ, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
      liftApply 0 (c 0 0) (fun _ => a₀) t X z = a₀ X)
    (a₀ : Vec 2 → ∀ i, hs i) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (X z : Vec 2) :
    liftApply 0 (hlDiagCoeff hs c 0 0) (fun _ => a₀) t X z = a₀ X := by
  funext v
  have h1 := congrFun (h0 (fun _ _ => 1) contDiff_const t ht X z) 0
  rw [liftApply_scalar_fin1] at h1
  rw [liftApply_hlDiag]
  simp only [zero_add, Finset.sum_range_one, Fintype.sum_unique, orderedDerivative_word_zero] at h1 ⊢
  rw [mul_one] at h1
  rw [h1, one_smul]

/-- Vanishing clauses (3) and (4): the candidate vanishes where the scalar array does. -/
theorem hlDiag_vanish (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ)) (n m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2)
    (h : c 0 n m α t X z 0 0 = 0) (v u : ι) :
    hlDiagCoeff hs c 0 n m α t X z v u = 0 := by
  rw [hlDiagCoeff_apply_zero, h]; simp

/-- Symmetry clause (5). -/
theorem hlDiag_symm (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ)) (n m : ℕ)
    (σ : Equiv.Perm (Fin m)) (α : DerivativeWord2 m)
    (h : c 0 n m (α ∘ σ) = c 0 n m α) :
    hlDiagCoeff hs c 0 n m (α ∘ σ) = hlDiagCoeff hs c 0 n m α := by
  funext t X z v u
  rw [hlDiagCoeff_apply_zero, hlDiagCoeff_apply_zero, h]

/-- Box smoothness and periodicity, clause (6). -/
theorem hlDiag_boxSmooth_periodic (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (sX sZ n m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (v u : ι)
    (hb : IsBoxSmooth sX sZ (fun X z => c 0 n m α t X z 0 0))
    (hp : ∀ X, AVenhance.IsZ2Periodic (fun z => c 0 n m α t X z 0 0)) :
    IsBoxSmooth sX sZ (fun X z => hlDiagCoeff hs c 0 n m α t X z v u) ∧
      ∀ X, AVenhance.IsZ2Periodic (fun z => hlDiagCoeff hs c 0 n m α t X z v u) := by
  constructor
  · have := hb.map_clm ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).smulRight (hlDiagMap hs v u))
    simpa [hlDiagCoeff_apply_zero] using this
  · intro X k x
    simp only [hlDiagCoeff_apply_zero]
    have := hp X k x
    simp only at this
    rw [this]

end

section
open Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.CycleComparison.Lift
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLMaps

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {hs : ι → Type*}
  [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)] {Dm : ℕ}

/-- The scalarization of a Hilbert field at the component `v` along `ℓ`. -/
def hlScal {v : ι} (ℓ : hs v →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ i, hs i) : ℝ → Vec 2 → Fin 1 → ℝ :=
  fun s Y _ => ℓ (a s Y v)

omit [DecidableEq ι] in
theorem hlScal_contDiff {v : ι} (ℓ : hs v →L[ℝ] ℝ) {a : ℝ → Vec 2 → ∀ i, hs i} {t : ℝ} {r : ℕ∞}
    (ha : ContDiff ℝ r (a t)) : ContDiff ℝ r (hlScal ℓ a t) := by
  refine contDiff_pi.mpr fun _ => ?_
  exact ℓ.contDiff.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := hs) v).contDiff.comp ha)

/-- `ℓ` of the `v` component of `liftApply` of the diagonal candidate is the scalar `liftApply` of
the scalarization. -/
theorem hl_liftApply_transfer (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ)) (n : ℕ)
    {v : ι} (ℓ : hs v →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ i, hs i) (t : ℝ) (X z : Vec 2)
    (ha : ContDiff ℝ (n : ℕ∞) (a t)) :
    ℓ (liftApply n (hlDiagCoeff hs c 0 n) a t X z v) =
      liftApply n (c 0 n) (hlScal ℓ a) t X z 0 := by
  rw [liftApply_hlDiag, liftApply_scalar_fin1, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hm1 : ContDiff ℝ (m : ℕ∞) (a t) := ha.of_le (by exact_mod_cast hmn)
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  have h2 : ContDiff ℝ (m : ℕ∞) (hlScal ℓ a t) := hlScal_contDiff ℓ hm1
  have h3 : ContDiff ℝ (m : ℕ∞) (fun Y => a t Y v) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v).contDiff.comp hm1
  rw [hl_orderedDerivative_proj α h2 X 0, hl_orderedDerivative_proj α hm1 X v]
  exact (hl_orderedDerivative_clm_apply ℓ α h3 X).symm

omit [DecidableEq ι] in
/-- Box smoothness of `liftA` at grade zero. -/
theorem liftA_boxSmooth_zero {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (n p q : ℕ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => Q.G t X i j))
    (hv : ∀ k, ContDiff ℝ (q : ℕ∞) (fun z => Q.v t z k))
    (ha : ContDiff ℝ ((p + 2 + n : ℕ) : ℕ∞) (a t))
    (hc : ∀ n' m α v u, IsBoxSmooth (p + 2) (q + 1) (fun X z => Cc 0 n' m α t X z v u)) :
    IsBoxSmooth p q (liftA Q Cc a 0 n t) := by
  have hG' : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => Q.G t Y i j) :=
    fun i j => isBoxSmooth_slow_field (p + 1) q _ (hG i j)
  have hF1 : IsBoxSmooth (p + 1) (q + 1) (liftApply (n - 1) (Cc 0 (n - 1)) a t) := by
    refine liftApply_box_reserve (n - 1) (p + 1) (q + 1) (Cc 0 (n - 1)) a t
      (ha.of_le (by exact_mod_cast (by omega))) fun m _ α v u => (hc (n - 1) m α v u).mono ?_ ?_
    <;> omega
  have hB1 := cellB1_box_reserve p q Q.η Q.G Q.v t _ hF1 hG'
    (fun k => isBoxSmooth_fast_field p q (fun z => Q.v t z k) (hv k))
  by_cases h2 : 2 ≤ n
  · have hF2 : IsBoxSmooth (p + 2) q (liftApply (n - 2) (Cc 0 (n - 2)) a t) := by
      refine liftApply_box_reserve (n - 2) (p + 2) q (Cc 0 (n - 2)) a t
        (ha.of_le (by exact_mod_cast (by omega))) fun m _ α v u => (hc (n - 2) m α v u).mono ?_ ?_
      <;> omega
    have hB2 := cellB2_box_reserve p q Q.η Q.G t _ hF2 hG'
    have e : liftA Q Cc a 0 n t = fun X z =>
        cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc 0 (n - 1)) a t) X z +
          cellB2 Q.η Q.G t (liftApply (n - 2) (Cc 0 (n - 2)) a t) X z := by
      funext X z
      simp [liftA, h2]
    rw [e]
    exact hB1.add hB2
  · have e : liftA Q Cc a 0 n t = cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc 0 (n - 1)) a t) := by
      funext X z
      simp [liftA, h2]
    rw [e]
    exact hB1

/-- `ℓ` of the `v` component of `liftA` of the diagonal candidate is the scalar `liftA` of the
scalarization (grade zero). -/
theorem hl_liftA_transfer (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v)
    {v : ι} (ℓ : hs v →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ i, hs i) (n : ℕ) (t : ℝ) (X z : Vec 2)
    (hGs : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j))
    (ha : ContDiff ℝ ((n + 2 : ℕ) : ℕ∞) (a t))
    (hcH : ∀ n' m α v' u, IsBoxSmooth 2 1 (fun X z => hlDiagCoeff hs c 0 n' m α t X z v' u))
    (hcS : ∀ n' m α v' u, IsBoxSmooth 2 1 (fun X z => c 0 n' m α t X z v' u)) :
    ℓ (liftA Q (hlDiagCoeff hs c) a 0 n t X z v) = liftA Q0 c (hlScal ℓ a) 0 n t X z 0 := by
  let Λ : (∀ i, hs i) →L[ℝ] ℝ := ℓ.comp (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v)
  let P0 : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
  have hG' : ∀ i j, IsBoxSmooth 1 0 (fun Y (_ : Vec 2) => Q.G t Y i j) :=
    fun i j => isBoxSmooth_slow_field 1 0 _ (hGs i j)
  have hrel : ∀ k, k ≤ n → ∀ Y y, Λ (liftApply k (hlDiagCoeff hs c 0 k) a t Y y) =
      P0 (liftApply k (c 0 k) (hlScal ℓ a) t Y y) := fun k hk Y y =>
    hl_liftApply_transfer c k ℓ a t Y y (ha.of_le (by exact_mod_cast (by omega)))
  have hF1H : IsBoxSmooth 1 1 (liftApply (n - 1) (hlDiagCoeff hs c 0 (n - 1)) a t) :=
    liftApply_box_reserve (n - 1) 1 1 _ a t (ha.of_le (by exact_mod_cast (by omega)))
      fun m _ α v' u => (hcH (n - 1) m α v' u).mono (by norm_num) le_rfl
  have hF1S : IsBoxSmooth 1 1 (liftApply (n - 1) (c 0 (n - 1)) (hlScal ℓ a) t) :=
    liftApply_box_reserve (n - 1) 1 1 _ (hlScal ℓ a) t
      ((hlScal_contDiff ℓ ha).of_le (by exact_mod_cast (by omega)))
      fun m _ α v' u => (hcS (n - 1) m α v' u).mono (by norm_num) le_rfl
  have hb1 : Λ (cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (hlDiagCoeff hs c 0 (n - 1)) a t) X z) =
      P0 (cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (c 0 (n - 1)) (hlScal ℓ a) t) X z) := by
    rw [← cellB1_postcomposition Λ Q.η Q.G Q.v t _ hF1H hG' X z,
      ← cellB1_postcomposition P0 Q.η Q.G Q.v t _ hF1S hG' X z]
    congr 1
    funext Y y
    exact hrel (n - 1) (by omega) Y y
  by_cases h2 : 2 ≤ n
  · have hF2H : IsBoxSmooth 2 0 (liftApply (n - 2) (hlDiagCoeff hs c 0 (n - 2)) a t) :=
      liftApply_box_reserve (n - 2) 2 0 _ a t (ha.of_le (by exact_mod_cast (by omega)))
        fun m _ α v' u => (hcH (n - 2) m α v' u).mono le_rfl (by norm_num)
    have hF2S : IsBoxSmooth 2 0 (liftApply (n - 2) (c 0 (n - 2)) (hlScal ℓ a) t) :=
      liftApply_box_reserve (n - 2) 2 0 _ (hlScal ℓ a) t
        ((hlScal_contDiff ℓ ha).of_le (by exact_mod_cast (by omega)))
        fun m _ α v' u => (hcS (n - 2) m α v' u).mono le_rfl (by norm_num)
    have hb2 : Λ (cellB2 Q.η Q.G t (liftApply (n - 2) (hlDiagCoeff hs c 0 (n - 2)) a t) X z) =
        P0 (cellB2 Q.η Q.G t (liftApply (n - 2) (c 0 (n - 2)) (hlScal ℓ a) t) X z) := by
      rw [← cellB2_postcomposition Λ Q.η Q.G t _ hF2H hG' X z,
        ← cellB2_postcomposition P0 Q.η Q.G t _ hF2S hG' X z]
      congr 1
      funext Y y
      exact hrel (n - 2) (by omega) Y y
    have eH : liftA Q (hlDiagCoeff hs c) a 0 n t X z =
        cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (hlDiagCoeff hs c 0 (n - 1)) a t) X z +
          cellB2 Q.η Q.G t (liftApply (n - 2) (hlDiagCoeff hs c 0 (n - 2)) a t) X z := by
      simp [liftA, h2]
    have eS : liftA Q0 c (hlScal ℓ a) 0 n t X z =
        cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (c 0 (n - 1)) (hlScal ℓ a) t) X z +
          cellB2 Q.η Q.G t (liftApply (n - 2) (c 0 (n - 2)) (hlScal ℓ a) t) X z := by
      simp [liftA, h2, hη, hG, hv]
    rw [eS]
    change Λ (liftA Q (hlDiagCoeff hs c) a 0 n t X z) = _
    rw [eH, map_add, hb1, hb2]
    rfl
  · have eH : liftA Q (hlDiagCoeff hs c) a 0 n t X z =
        cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (hlDiagCoeff hs c 0 (n - 1)) a t) X z := by
      simp [liftA, h2]
    have eS : liftA Q0 c (hlScal ℓ a) 0 n t X z =
        cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (c 0 (n - 1)) (hlScal ℓ a) t) X z := by
      simp [liftA, h2, hη, hG, hv]
    rw [eS]
    change Λ (liftA Q (hlDiagCoeff hs c) a 0 n t X z) = _
    rw [eH, hb1]
    rfl

omit [DecidableEq ι] in
/-- The mean of the grade-zero `liftA` is smooth in the slow variable. -/
theorem liftMean_contDiff_zero {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)] (Q : LiftOperatorData ι h Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (n j : ℕ) (t : ℝ)
    (hG : ∀ i k, ContDiff ℝ ((j + 1 : ℕ) : ℕ∞) (fun X => Q.G t X i k))
    (hv : ∀ k, ContDiff ℝ (j : ℕ∞) (fun z => Q.v t z k))
    (ha : ContDiff ℝ ((j + 2 + n : ℕ) : ℕ∞) (a t))
    (hc : ∀ n' m α v u, IsBoxSmooth (j + 2) (j + 1) (fun X z => Cc 0 n' m α t X z v u)) :
    ContDiff ℝ (j : ℕ∞) (liftMean Q Cc a 0 n t) := by
  have hb := liftA_boxSmooth_zero Q Cc a n j j t hG hv ha
    (fun n' m α v u => (hc n' m α v u).mono le_rfl (by omega))
  exact AVRegularity.Providers.PathDecomp.contDiff_fieldCellMean (hb.contDiff_uncurry le_rfl le_rfl)

omit [DecidableEq ι] in
theorem liftA_continuous_slice_zero {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Q : LiftOperatorData ι h Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ)
    (hG : ∀ i k, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i k))
    (hv : ∀ k, ContDiff ℝ (0 : ℕ∞) (fun z => Q.v t z k))
    (ha : ContDiff ℝ ((2 + n : ℕ) : ℕ∞) (a t))
    (hc : ∀ n' m α v u, IsBoxSmooth 2 1 (fun X z => Cc 0 n' m α t X z v u)) (X : Vec 2) :
    Continuous (fun z => liftA Q Cc a 0 n t X z) := by
  have hb := liftA_boxSmooth_zero Q Cc a n 0 0 t hG hv ha hc
  exact (boxSmooth_continuous hb).comp (continuous_const.prodMk continuous_id)

/-- `ℓ` of the `v` component of `liftMean` of the diagonal candidate (grade zero). -/
theorem hl_liftMean_transfer [∀ i, CompleteSpace (hs i)]
    (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v)
    {v : ι} (ℓ : hs v →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ i, hs i) (n : ℕ) (t : ℝ) (X : Vec 2)
    (hGs : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ k, ContDiff ℝ (0 : ℕ∞) (fun z => Q.v t z k))
    (ha : ContDiff ℝ ((n + 2 : ℕ) : ℕ∞) (a t))
    (hcH : ∀ n' m α v' u, IsBoxSmooth 2 1 (fun X z => hlDiagCoeff hs c 0 n' m α t X z v' u))
    (hcS : ∀ n' m α v' u, IsBoxSmooth 2 1 (fun X z => c 0 n' m α t X z v' u)) :
    ℓ (liftMean Q (hlDiagCoeff hs c) a 0 n t X v) = liftMean Q0 c (hlScal ℓ a) 0 n t X 0 := by
  let Λ : (∀ i, hs i) →L[ℝ] ℝ := ℓ.comp (ContinuousLinearMap.proj (R := ℝ) (φ := hs) v)
  let P0 : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
  have hcontH := liftA_continuous_slice_zero Q (hlDiagCoeff hs c) a n t hGs hvs
    (by simpa [add_comm] using ha) hcH X
  have hcontS := liftA_continuous_slice_zero Q0 c (hlScal ℓ a) n t (by rw [hG]; exact hGs)
    (by rw [hv]; exact hvs) (by simpa [add_comm] using hlScal_contDiff ℓ ha) hcS X
  change Λ (fieldCellMean (fun z => liftA Q (hlDiagCoeff hs c) a 0 n t X z)) =
    P0 (fieldCellMean (fun z => liftA Q0 c (hlScal ℓ a) 0 n t X z))
  rw [← fieldCellMean_clm Λ hcontH, ← fieldCellMean_clm P0 hcontS]
  congr 1
  funext z
  exact hl_liftA_transfer c Q Q0 hη hG hv ℓ a n t X z hGs ha hcH hcS

/-- `ℓ` of the `v` component of the grade-zero cell source of the diagonal candidate. -/
theorem hl_liftCellSource_transfer [∀ i, CompleteSpace (hs i)]
    (c : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ))
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v)
    {v : ι} (ℓ : hs v →L[ℝ] ℝ) (a : ℝ → Vec 2 → ∀ i, hs i) (n : ℕ) (t : ℝ) (X z : Vec 2)
    (hGs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun z => Q.v t z k))
    (ha : ContDiff ℝ ((n + 2 : ℕ) : ℕ∞) (a t))
    (hcH : ∀ n' m α v' u, IsBoxSmooth (n + 2) (n + 2)
      (fun X z => hlDiagCoeff hs c 0 n' m α t X z v' u))
    (hcS : ∀ n' m α v' u, IsBoxSmooth (n + 2) (n + 2) (fun X z => c 0 n' m α t X z v' u)) :
    ℓ (liftCellSource Q (hlDiagCoeff hs c) a 0 n t X z v) =
      liftCellSource Q0 c (hlScal ℓ a) 0 n t X z 0 := by
  have hGl : ∀ r : ℕ, ∀ i j, ContDiff ℝ (r : ℕ∞) (fun X => Q.G t X i j) :=
    fun r i j => (hGs i j).of_le (by exact_mod_cast le_top)
  have hvl : ∀ r : ℕ, ∀ k, ContDiff ℝ (r : ℕ∞) (fun z => Q.v t z k) :=
    fun r k => (hvs k).of_le (by exact_mod_cast le_top)
  have hcH' : ∀ p q, p ≤ n + 2 → q ≤ n + 2 → ∀ n' m α v' u,
      IsBoxSmooth p q (fun X z => hlDiagCoeff hs c 0 n' m α t X z v' u) :=
    fun p q hp hq n' m α v' u => (hcH n' m α v' u).mono hp hq
  have hcS' : ∀ p q, p ≤ n + 2 → q ≤ n + 2 → ∀ n' m α v' u,
      IsBoxSmooth p q (fun X z => c 0 n' m α t X z v' u) :=
    fun p q hp hq n' m α v' u => (hcS n' m α v' u).mono hp hq
  have hM : ∀ k, k ≤ n → ∀ Y, hlScal ℓ (liftMean Q (hlDiagCoeff hs c) a 0 k) t Y =
      liftMean Q0 c (hlScal ℓ a) 0 k t Y := by
    intro k hk Y
    funext i
    rw [Subsingleton.elim i 0]
    exact hl_liftMean_transfer c Q Q0 hη hG hv ℓ a k t Y (hGl 1) (hvl 0)
      (ha.of_le (by exact_mod_cast (by omega))) (hcH' 2 1 (by omega) (by omega))
      (hcS' 2 1 (by omega) (by omega))
  unfold liftCellSource
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Pi.add_apply, Pi.neg_apply,
    Pi.sub_apply, Finset.sum_apply]
  rw [map_add, map_neg, map_sub, map_sum]
  congr 1
  · congr 1
    congr 1
    · exact hl_liftA_transfer c Q Q0 hη hG hv ℓ a n t X z (hGl 1)
        (ha.of_le (by exact_mod_cast (by omega))) (hcH' 2 1 (by omega) (by omega))
        (hcS' 2 1 (by omega) (by omega))
    · exact hl_liftMean_transfer c Q Q0 hη hG hv ℓ a n t X (hGl 1) (hvl 0) ha
        (hcH' 2 1 (by omega) (by omega)) (hcS' 2 1 (by omega) (by omega))
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    have hmc : ContDiff ℝ (j : ℕ∞) (liftMean Q (hlDiagCoeff hs c) a 0 (n - j) t) :=
      liftMean_contDiff_zero Q (hlDiagCoeff hs c) a (n - j) j t (hGl (j + 1)) (hvl j)
        (ha.of_le (by exact_mod_cast (by omega)))
        (fun n' m α v' u => hcH' (j + 2) (j + 1) (by omega) (by omega) n' m α v' u)
    rw [hl_liftApply_transfer c j ℓ _ t X z hmc]
    have hw : hlScal ℓ (liftMean Q (hlDiagCoeff hs c) a 0 (n - j)) t =
        liftMean Q0 c (hlScal ℓ a) 0 (n - j) t := funext (hM (n - j) (by omega))
    simp only [liftApply, hw]

end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLZero
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg

/-! Spatial regularity of the Eulerian flux of one pulse.

`pulseMeanFluxEuler` is `C^s` in the Eulerian variable if the chart is `C^{s+Dm+N}`, the label is `C^s`,
the coarse field is `C^{s+Dm+N}` and the lift data satisfy the hypotheses of `liftFluxX_box` at the
pulse clock `c⁻¹ t`. -/

/-- A Jacobian entry of a `C^{s+1}` chart along a `C^s` label is `C^s`. -/
theorem jacMatrix_entry_contDiff {f : Vec 2 → Vec 2} {s : ℕ}
    (hf : ContDiff ℝ ((s + 1 : ℕ) : ℕ∞) f) {g : Vec 2 → Vec 2} (hg : ContDiff ℝ (s : ℕ∞) g)
    (j k : Fin 2) : ContDiff ℝ (s : ℕ∞) (fun y => jacMatrix f (g y) j k) := by
  have h1 : ContDiff ℝ (s : ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := (s : ℕ∞)) (by exact_mod_cast le_rfl)
  have h2 : ContDiff ℝ (s : ℕ∞) (fun y => fderiv ℝ f (g y) (basisVec k)) :=
    (h1.comp hg).clm_apply contDiff_const
  exact (contDiff_pi.mp h2) j

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)] {Dm : ℕ}

/-- **Regularity of the Eulerian flux of one pulse.** -/
theorem pulseMeanFluxEuler_contDiff (c ρ εc : ℝ) (n r : ℕ) (Q : LiftOperatorData ι h Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i)
    (t : ℝ) (v : ι) (s N H : ℕ) (hc : c ≠ 0) (hDm : 1 ≤ Dm) (hrH : r ≤ H)
    (hz : ∀ hh' ≤ H, ∀ n', N < n' → ∀ m α t X z v u, Cc hh' n' m α t X z v u = 0)
    (hb : ∀ hh' ≤ H, ∀ n' m α v u,
      IsBoxSmooth (s + Dm) (s + Dm) (fun X z => Cc hh' n' m α (c⁻¹ * t) X z v u))
    (hG : ∀ k j, ContDiff ℝ (s : ℕ∞) (fun X => Q.G (c⁻¹ * t) X k j))
    (hv : ∀ k, ContDiff ℝ (s : ℕ∞) (fun z => Q.v (c⁻¹ * t) z k))
    (hedge : r ≠ 0 → ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth s s (fun X z => γ.coeff α (c⁻¹ * t) X z))
    (ha : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (a t))
    (hchart : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (chart t))
    (hlabel : ContDiff ℝ (s : ℕ∞) (label t)) :
    ContDiff ℝ (s : ℕ∞) (fun y => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a t y v) := by
  have hclk : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have ha' : ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞)
      ((fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) (c⁻¹ * t)) := by
    show ContDiff ℝ ((s + Dm + N : ℕ) : ℕ∞) (fun X' => a (c * (c⁻¹ * t))
      (chart (c * (c⁻¹ * t)) (ρ • X')))
    rw [hclk]
    exact ha.comp (hchart.comp (contDiff_const_smul ρ))
  have hchart1 : ContDiff ℝ ((s + 1 : ℕ) : ℕ∞) (chart t) :=
    hchart.of_le (by exact_mod_cast (by omega : s + 1 ≤ s + Dm + N))
  have hM : ∀ k : Fin 2, ContDiff ℝ (s : ℕ∞) (fun X => fieldCellMean (fun z =>
      liftFluxX Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) r n (c⁻¹ * t) X z k)) := by
    intro k
    have hW := liftFluxX_box Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) r n
      (c⁻¹ * t) k s N H hDm hrH hz hb (hG k) (hv k) hedge ha'
    exact AVRegularity.Providers.PathDecomp.contDiff_fieldCellMean
      (hW.contDiff_uncurry le_rfl le_rfl)
  unfold pulseMeanFluxEuler
  refine contDiff_pi.mpr fun j => ?_
  refine ContDiff.sum fun k _ => ?_
  refine ContDiff.smul (jacMatrix_entry_contDiff hchart1 hlabel j k) ?_
  refine ContDiff.const_smul _ ?_
  have h1 : ContDiff ℝ (s : ℕ∞) (fun y => fieldCellMean (fun z =>
      liftFluxX Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) r n (c⁻¹ * t)
        (ρ⁻¹ • label t y) z k)) :=
    (hM k).comp (hlabel.const_smul ρ⁻¹)
  exact (contDiff_pi.mp h1) v

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! The finer-output step of the flux cancellation, abstract part: **slow translations of lift sequences**.

Two lift operator data `Q'`, `Q` are *related by the slow translation `T`* when they have the same
contrast and drift, `Q'.G t X = Q.G t (X + T)`, and the source edges of `Q'` at `X` are those of
`Q` at `X + T`. The edge relation is asked at one time (`EdgesShiftAt T t`): for the families of a
stage it comes from the context formula of the old fluxes, which is known on the pulse window
only.

* The operators of the lift recursion (`𝒮_ε`, `ℬ_1`, `ℬ_2`, `𝐀_n`, the means, the cell sources and
  the slow fluxes `liftFluxX`) are covariant under a related pair of data, at that time
  (`liftCellSource_shiftRel`, `liftFluxX_shiftRel`). The proofs are those of
  `CycleComparison.LiftMeanEntrywise` for invariant data.
* `liftSequence_shift_covariant`: if the data are related on the cell-time window, the lift
  sequence of `Q'` on `{X | X + T ∈ Ω}` is the translate of the lift sequence of `Q` on `Ω`
  (uniqueness of the cell inverse on the window, as in `lift_sequence_unique_window_on`). -/

open CycleComparison.LiftMeanEntrywise Uniqueness

section Frame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `ℬ_1` of a translated field, for a translated metric. -/
theorem cellB1_metricShift (η : ℝ) (G' G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (Φ : Vec 2 → Vec 2 → E) (T : Vec 2)
    (hG : ∀ X i j, G' t X i j = G t (X + T) i j) (X z : Vec 2) :
    cellB1 η G' v t (fun X' z' => Φ (X' + T) z') X z = cellB1 η G v t Φ (X + T) z := by
  have hs (j : Fin 2) : slowPartial j (fun X' z' => Φ (X' + T) z') =
      fun X' z' => slowPartial j Φ (X' + T) z' := by
    funext X' z'
    exact slowPartial_slowShift j Φ T X' z'
  have hg (i j : Fin 2) :
      (fun X' z' => G' t X' i j • fastPartial j (fun X'' z'' => Φ (X'' + T) z'') X' z') =
        fun X' z' => (fun Y y => G t Y i j • fastPartial j Φ Y y) (X' + T) z' := by
    funext X' z'
    simp only [hG]
    rfl
  have h1 (k : Fin 2) : slowPartial k (fun X' z' => Φ (X' + T) z') X z =
      slowPartial k Φ (X + T) z := slowPartial_slowShift k Φ T X z
  have h2 (i j : Fin 2) : fastPartial i (slowPartial j (fun X' z' => Φ (X' + T) z')) X z =
      fastPartial i (slowPartial j Φ) (X + T) z := by
    rw [hs j]
    rfl
  have h3 (i j : Fin 2) :
      slowPartial i (fun X' z' => G' t X' i j •
        fastPartial j (fun X'' z'' => Φ (X'' + T) z'') X' z') X z =
      slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') (X + T) z := by
    rw [hg i j]
    exact slowPartial_slowShift i (fun Y y => G t Y i j • fastPartial j Φ Y y) T X z
  simp only [cellB1, h1, h2, h3]
  simp only [hG]

/-- `ℬ_2` of a translated field, for a translated metric. -/
theorem cellB2_metricShift (η : ℝ) (G' G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (Φ : Vec 2 → Vec 2 → E) (T : Vec 2) (hG : ∀ X i j, G' t X i j = G t (X + T) i j)
    (X z : Vec 2) :
    cellB2 η G' t (fun X' z' => Φ (X' + T) z') X z = cellB2 η G t Φ (X + T) z := by
  have hg (i j : Fin 2) :
      (fun X' z' => G' t X' i j • slowPartial j (fun X'' z'' => Φ (X'' + T) z'') X' z') =
        fun X' z' => (fun Y y => G t Y i j • slowPartial j Φ Y y) (X' + T) z' := by
    funext X' z'
    simp only [slowPartial_slowShift, hG]
  have h4 (i j : Fin 2) :
      slowPartial i (fun X' z' => G' t X' i j •
        slowPartial j (fun X'' z'' => Φ (X'' + T) z'') X' z') X z =
      slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') (X + T) z := by
    rw [hg i j]
    exact slowPartial_slowShift i (fun Y y => G t Y i j • slowPartial j Φ Y y) T X z
  simp only [cellB2, h4]

end Frame

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

/-- The edges `e'` at the slow offset `X` are the edges `e` at `X + T`, at the time `t`: the same
lists of maps, and coefficients related by the translation. -/
def EdgesShiftAt (T : Vec 2) (t : ℝ) (e' e : ConstituentEdges Dm h) : Prop :=
  ∀ v u d, List.Forall₂ (fun γ' γ => γ'.map = γ.map ∧
    ∀ α X z, γ'.coeff α t X z = γ.coeff α t (X + T) z) (e' v u d) (e v u d)

theorem sourceFlux_edgesShift {T : Vec 2} {t : ℝ} {e' e : ConstituentEdges Dm h}
    (he : EdgesShiftAt T t e' e) (η ε : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2)
    (X z : Vec 2) :
    sourceFlux e' η ε t (fun X' z' => Φ (X' + T) z') k X z =
      sourceFlux e η ε t Φ k (X + T) z := by
  funext v
  simp only [sourceFlux, dEpsWord_slowShift]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  exact list_sum_map_forall₂ (he v u d) fun γ' γ hγ => by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hγ.2 α X z, hγ.1]

theorem sourceOp_edgesShift {T : Vec 2} {t : ℝ} {e' e : ConstituentEdges Dm h}
    (he : EdgesShiftAt T t e' e) (η ε : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X z : Vec 2) :
    sourceOp e' η ε t (fun X' z' => Φ (X' + T) z') X z = sourceOp e η ε t Φ (X + T) z := by
  have hf (k : Fin 2) : sourceFlux e' η ε t (fun X' z' => Φ (X' + T) z') k =
      fun X' z' => sourceFlux e η ε t Φ k (X' + T) z' := by
    funext X' z'
    exact sourceFlux_edgesShift he η ε Φ k X' z'
  simp only [sourceOp, hf, dEps_slowShift]

theorem sourceCoeff_edgesShift {T : Vec 2} {t : ℝ} {e' e : ConstituentEdges Dm h}
    (he : EdgesShiftAt T t e' e) (η : ℝ) (j : ℕ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X z : Vec 2) :
    sourceCoeff e' η j t (fun X' z' => Φ (X' + T) z') X z =
      sourceCoeff e η j t Φ (X + T) z := by
  have hE : (fun ε => sourceOp e' η ε t (fun X' z' => Φ (X' + T) z') X z) =
      fun ε => sourceOp e η ε t Φ (X + T) z :=
    funext fun ε => sourceOp_edgesShift he η ε Φ X z
  simp only [sourceCoeff, hE]

/-- `𝐀_n` is covariant under data related by the slow translation at the time `t`. -/
theorem liftA_shiftRel (Q' Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (t : ℝ) (hη : Q'.η = Q.η) (hv : Q'.v = Q.v)
    (hG : ∀ X i j, Q'.G t X i j = Q.G t (X + T) i j) (he : EdgesShiftAt T t Q'.edge Q.edge)
    (hab : ∀ Y, b t Y = a t (Y + T)) (hh n : ℕ) (X z : Vec 2) :
    liftA Q' (slowShiftSequence T Cc) b hh n t X z = liftA Q Cc a hh n t (X + T) z := by
  have hL (q p : ℕ) : liftApply q (slowShiftCoeff T (Cc p q)) b t =
      fun X' z' => liftApply q (Cc p q) a t (X' + T) z' := by
    funext X' z'
    exact liftApply_slowShift q (Cc p q) a b T t hab X' z'
  have hB1 (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X' z' : Vec 2) :
      cellB1 Q'.η Q'.G Q'.v t (fun Y y => Φ (Y + T) y) X' z' =
        cellB1 Q.η Q.G Q.v t Φ (X' + T) z' := by
    rw [hη, hv]
    exact cellB1_metricShift Q.η Q'.G Q.G Q.v t Φ T hG X' z'
  have hB2 (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X' z' : Vec 2) :
      cellB2 Q'.η Q'.G t (fun Y y => Φ (Y + T) y) X' z' = cellB2 Q.η Q.G t Φ (X' + T) z' := by
    rw [hη]
    exact cellB2_metricShift Q.η Q'.G Q.G t Φ T hG X' z'
  have hS (j : ℕ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X' z' : Vec 2) :
      sourceCoeff Q'.edge Q'.η j t (fun Y y => Φ (Y + T) y) X' z' =
        sourceCoeff Q.edge Q.η j t Φ (X' + T) z' := by
    rw [hη]
    exact sourceCoeff_edgesShift he Q.η j Φ X' z'
  simp only [liftA, hL, hB1, hB2, hS]

theorem liftMean_shiftRel (Q' Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (t : ℝ) (hη : Q'.η = Q.η) (hv : Q'.v = Q.v)
    (hG : ∀ X i j, Q'.G t X i j = Q.G t (X + T) i j) (he : EdgesShiftAt T t Q'.edge Q.edge)
    (hab : ∀ Y, b t Y = a t (Y + T)) (hh n : ℕ) (X : Vec 2) :
    liftMean Q' (slowShiftSequence T Cc) b hh n t X = liftMean Q Cc a hh n t (X + T) := by
  have hz : (fun z => liftA Q' (slowShiftSequence T Cc) b hh n t X z) =
      fun z => liftA Q Cc a hh n t (X + T) z :=
    funext fun z => liftA_shiftRel Q' Q Cc a b T t hη hv hG he hab hh n X z
  change fieldCellMean (fun z => liftA Q' (slowShiftSequence T Cc) b hh n t X z) =
    fieldCellMean (fun z => liftA Q Cc a hh n t (X + T) z)
  rw [hz]

/-- The cell source of the lift recursion is covariant under data related by the slow translation
at the time `t`. -/
theorem liftCellSource_shiftRel (Q' Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (t : ℝ) (hη : Q'.η = Q.η) (hv : Q'.v = Q.v)
    (hG : ∀ X i j, Q'.G t X i j = Q.G t (X + T) i j) (he : EdgesShiftAt T t Q'.edge Q.edge)
    (hab : ∀ Y, b t Y = a t (Y + T)) (hh n : ℕ) (X z : Vec 2) :
    liftCellSource Q' (slowShiftSequence T Cc) b hh n t X z =
      liftCellSource Q Cc a hh n t (X + T) z := by
  have hT (j : ℕ) (p : ℕ × ℕ) : liftApply j (slowShiftSequence T Cc p.1 j)
      (liftMean Q' (slowShiftSequence T Cc) b p.2 (n - j)) t X z =
      liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t (X + T) z :=
    liftApply_slowShift j (Cc p.1 j) _ _ T t
      (fun Y => liftMean_shiftRel Q' Q Cc a b T t hη hv hG he hab p.2 (n - j) Y) X z
  change -(liftA Q' (slowShiftSequence T Cc) b hh n t X z -
      liftMean Q' (slowShiftSequence T Cc) b hh n t X) +
      (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (slowShiftSequence T Cc p.1 j)
          (liftMean Q' (slowShiftSequence T Cc) b p.2 (n - j)) t X z) =
    -(liftA Q Cc a hh n t (X + T) z - liftMean Q Cc a hh n t (X + T)) +
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t (X + T) z
  rw [liftA_shiftRel Q' Q Cc a b T t hη hv hG he hab,
    liftMean_shiftRel Q' Q Cc a b T t hη hv hG he hab]
  simp only [hT]

/-- The slow flux of `𝐀_n` is covariant under data related by the slow translation at the time
`t`. -/
theorem liftFluxX_shiftRel (Q' Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (T : Vec 2) (t : ℝ) (hη : Q'.η = Q.η) (hv : Q'.v = Q.v)
    (hG : ∀ X i j, Q'.G t X i j = Q.G t (X + T) i j) (he : EdgesShiftAt T t Q'.edge Q.edge)
    (hab : ∀ Y, b t Y = a t (Y + T)) (hh n : ℕ) (X z : Vec 2) (k : Fin 2) :
    liftFluxX Q' (slowShiftSequence T Cc) b hh n t X z k =
      liftFluxX Q Cc a hh n t (X + T) z k := by
  have hL (q p : ℕ) : liftApply q (slowShiftCoeff T (Cc p q)) b t =
      fun X' z' => liftApply q (Cc p q) a t (X' + T) z' := by
    funext X' z'
    exact liftApply_slowShift q (Cc p q) a b T t hab X' z'
  have hF (j : Fin 2) (Φ : Vec 2 → Vec 2 → ∀ i, h i) :
      fastPartial j (fun X' z' => Φ (X' + T) z') X z = fastPartial j Φ (X + T) z := rfl
  have hS (j : Fin 2) (Φ : Vec 2 → Vec 2 → ∀ i, h i) :
      slowPartial j (fun X' z' => Φ (X' + T) z') X z = slowPartial j Φ (X + T) z :=
    slowPartial_slowShift j Φ T X z
  have hE (Φ : Vec 2 → Vec 2 → ∀ i, h i) :
      (fun ε : ℝ => sourceFlux Q'.edge Q.η ε t (fun X' z' => Φ (X' + T) z') k X z) =
        fun ε => sourceFlux Q.edge Q.η ε t Φ k (X + T) z := by
    funext ε
    exact sourceFlux_edgesShift he Q.η ε Φ k X z
  unfold liftFluxX
  simp only [hL, hF, hS, hE, hG, hη, hv]

/-- **The lift sequence of translated data is the translated lift sequence.** `Q'` and `Q` are
related by the slow translation `T` on the cell-time window (the metric at every time), `Cc'` is
a lift sequence of `Q'` on `{X | X + T ∈ Ω}` and `Cc` one of `Q` on the open set `Ω`. -/
theorem liftSequence_shift_covariant [∀ i, FiniteDimensional ℝ (h i)]
    (Q' Q : LiftOperatorData ι h Dm) (T : Vec 2) (t₀ t₁ : ℝ) (hab : t₀ ≤ t₁)
    {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) (hη : Q'.η = Q.η) (hv : Q'.v = Q.v)
    (hG : ∀ t X i j, Q'.G t X i j = Q.G t (X + T) i j)
    (he : ∀ t ∈ Icc t₀ t₁, EdgesShiftAt T t Q'.edge Q.edge)
    (hW : ∀ X, X + T ∈ Ω → ∃ lo A Mv : ℝ,
      WindowData (fun t => Matrix.of (Q'.G t X)) Q'.v t₀ t₁ lo A Mv)
    (sX sZ N H : ℕ) (Cc' Cc : ℕ → ℕ → LiftCoeff ι h)
    (hC' : IsLiftSequenceOn {X | X + T ∈ Ω} Q' sX sZ t₀ t₁ N H Cc')
    (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc) :
    ∀ hh ≤ H, ∀ n m (α : DerivativeWord2 m), ∀ t ∈ Icc t₀ t₁, ∀ X, X + T ∈ Ω → ∀ z v u,
      Cc' hh n m α t X z v u = Cc hh n m α t (X + T) z v u := by
  classical
  have hΩ' : IsOpen {X : Vec 2 | X + T ∈ Ω} := hΩ.preimage (continuous_id.add continuous_const)
  have hshift (a₀ : Vec 2 → ∀ i, h i) : ∀ s Y,
      (fun (_ : ℝ) => a₀) s Y = (fun (_ : ℝ) (Y' : Vec 2) => a₀ (Y' - T)) s (Y + T) := by
    intro s Y
    simp only [add_sub_cancel_right]
  have hsmooth (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) :
      ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => a₀ (Y - T)) :=
    ha₀.comp (contDiff_id.sub contDiff_const)
  have main : ∀ hh ≤ H, ∀ n,
      CoeffEqOn {X : Vec 2 | X + T ∈ Ω} Cc' (slowShiftSequence T Cc) t₀ t₁ hh n := by
    intro hh
    induction hh using Nat.strong_induction_on with
    | _ hh ihh =>
    intro hhH n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    have IH : ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) →
        CoeffEqOn {X : Vec 2 | X + T ∈ Ω} Cc' (slowShiftSequence T Cc) t₀ t₁ hh' n' := by
      intro hh' n' hlt
      rcases hlt with hlt | ⟨rfl, hn⟩
      · exact ihh hh' hlt (by omega) n'
      · exact ihn n' hn
    have det : ∀ t ∈ Icc t₀ t₁, ∀ X z, (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
        liftApply n (Cc' hh n) (fun _ => a₀) t X z =
          liftApply n (slowShiftSequence T Cc hh n) (fun _ => a₀) t X z) →
        ∀ m (α : DerivativeWord2 m), ∀ v u,
          Cc' hh n m α t X z v u = slowShiftSequence T Cc hh n m α t X z v u := by
      intro t _ X z hap m α v u
      by_cases hmn : m ≤ n
      · exact coeff_eq_of_apply_eq n (Cc' hh n) (slowShiftSequence T Cc hh n)
          (fun m α σ => (hC'.2.2.2.2.1 hh hhH n m α σ))
          (fun m α σ => by
            funext t X z
            exact congrFun (congrFun (congrFun (hC.2.2.2.2.1 hh hhH n m α σ) t) (X + T)) z)
          t X z hap m hmn α v u
      · have hmn' := not_le.mp hmn
        rw [hC'.2.2.2.1 hh hhH n m hmn' α t X z v u]
        exact (hC.2.2.2.1 hh hhH n m hmn' α t (X + T) z v u).symm
    intro t ht m α X hX
    funext z v u
    by_cases hn0 : n = 0
    · subst hn0
      by_cases hh0 : hh = 0
      · subst hh0
        refine det t ht X z (fun a₀ ha₀ => ?_) m α v u
        rw [hC'.1 a₀ ha₀ t ht X z,
          liftApply_slowShift 0 (Cc 0 0) (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t
            (hshift a₀ t) X z,
          hC.1 _ (hsmooth a₀ ha₀) t ht (X + T) z]
        simp only [add_sub_cancel_right]
      · rw [hC'.2.1 hh (by omega) hhH m α t X z v u]
        exact (hC.2.1 hh (by omega) hhH m α t (X + T) z v u).symm
    · by_cases hnN : N < n
      · rw [hC'.2.2.1 hh hhH n hnN m α t X z v u]
        exact (hC.2.2.1 hh hhH n hnN m α t (X + T) z v u).symm
      · have hnN' := not_lt.mp hnN
        refine det t ht X z (fun a₀ ha₀ => ?_) m α v u
        obtain ⟨lo, A, Mv, hWX⟩ := hW X hX
        have hcX' := hC'.2.2.2.2.2.2 hh hhH n (by omega) hnN' a₀ ha₀ X hX
        have hcX := hC.2.2.2.2.2.2 hh hhH n (by omega) hnN' _ (hsmooth a₀ ha₀) (X + T) hX
        have hGm : (fun t => Matrix.of (Q.G t (X + T))) = fun t => Matrix.of (Q'.G t X) := by
          funext t
          congr 1
          funext i j
          exact (hG t X i j).symm
        rw [hGm, ← hv] at hcX
        have hsrc : ∀ t ∈ Icc t₀ t₁, ∀ z, liftCellSource Q' Cc' (fun _ => a₀) hh n t X z =
            liftCellSource Q Cc (fun _ Y => a₀ (Y - T)) hh n t (X + T) z := fun t ht z => by
          rw [liftCellSource_locEq Q' (Cc := Cc') (Cc' := slowShiftSequence T Cc) hΩ' hh n
            (by omega) IH ht (fun _ => a₀) X hX z]
          exact liftCellSource_shiftRel Q' Q Cc (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t hη hv
            (hG t) (he t ht) (hshift a₀ t) hh n X z
        rw [cellField_unique_window hab hWX (fun t ht z => hsrc t ht z) hcX' hcX t ht z]
        exact (liftApply_slowShift n (Cc hh n) (fun _ Y => a₀ (Y - T)) (fun _ => a₀) T t
          (hshift a₀ t) X z).symm
  intro hh hhH n m α t ht X hX z v u
  exact congrFun (congrFun (congrFun (main hh hhH n t ht m α X hX) z) v) u

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLDecomp

/-! The path-sum step at positive grades: the generic path decomposition `PathDecomp.decomp` for a stage
whose path lifts are GLOBAL lift sequences, without a lift setting.

`PathDecomp.StageSetting` builds the uniqueness-step hypotheses `StepHyp` of the stage and of its
path families from an `IsLiftSetting` of the fibre data. On the native chain of a pulse the lift
relation of the successor holds at every slow offset and the flux coefficients of the actual
contexts are jointly smooth, so the same hypotheses follow from regularity facts stated directly:

* `Setting`: the window, the window data of the cell equation, the regularity of the metric, of
  the drift and of the step data of the stage, the global lift sequences of the path families of
  at most `h` edges (the empty path included), and the regularity indices.
* `Setting.stageHyp`, `Setting.chainHyp`, `Setting.chainHyps`: the hypotheses `StepHyp`, for
  `2 ≤ Dm` (the explicit formulas of the cell source ask for it).
* `Decomposed`: the conclusion of the decomposition: the lift of the fibre and the lift of every
  path family agree on the window with the path-candidate arrays of the top entries `hlTop`.
* `Setting.decomposed`: `Setting` and `2 ≤ Dm` give `Decomposed`. -/

open AVRegularity.Providers.PathDecomp AVRegularity.Uniqueness

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The top arrays of the chosen path lifts of the paths of at most `h` edges. -/
def hlTop (G : GenStage D hr Dm b j₀) (m : ℕ) (ρ : ℝ) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) (h : ℕ)
    (Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) :
    (g : ℕ) → (Fin g → StepDat) → SArr :=
  topOf (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ)
    (stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h)

/-- The hypotheses of the path decomposition of a stage on a chain, stated without a lift
setting. -/
structure Setting (G : GenStage D hr Dm b j₀) (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ)
    (p : OddSlot) (c : StageCtx D b j₀ G.level p) (t₀ t₁ : ℝ) (h N sX sZ : ℕ)
    (Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) : Prop where
  window : t₀ ≤ t₁
  windowData : ∀ X : Vec 2, ∃ lo A' Mv : ℝ, WindowData
    (fun t => Matrix.of ((familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c)).G t X))
    (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c)).v t₀ t₁ lo A' Mv
  metric : ∀ t ∈ Icc t₀ t₁, ∀ a b', ContDiff ℝ ((N + 2 : ℕ) : ℕ∞) (fun X =>
    (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c)).G t X a b')
  drift : ∀ t ∈ Icc t₀ t₁, ∀ κ, GoodField (N + 2) (fun (_ z : Vec 2) =>
    (familyLiftData (ι := CompIn G.comps) D m k A ρ (G.fam.fiber p c)).v t z κ)
  goodDat : ∀ (v u : CompIn G.comps) (γ : G.fam.Γ v u), ∀ t ∈ Icc t₀ t₁,
    GoodDat (N + 1 + Dm) t (stageDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c v u γ)
  hπ : ∀ h' ≤ h, ∀ σ : StagePath G h', IsLiftSequence
    (familyLiftData D m k A ρ (pathEdges G σ p c)) sX sZ t₀ t₁ N h' (Ccπ h' σ)
  hsX : N + 1 + Dm ≤ sX
  hsZ : N + 1 + Dm ≤ sZ

/-- The conclusion of the path decomposition: the lift of the fibre and the lifts of the path
families are, on the window, the path-candidate arrays of the top entries of the path lifts. -/
structure Decomposed (G : GenStage D hr Dm b j₀) (m : ℕ) (ρ : ℝ)
    (p : OddSlot) (c : StageCtx D b j₀ G.level p) (t₀ t₁ : ℝ) (h : ℕ)
    (CcT : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) : Prop where
  stage : ∀ g ≤ h, ∀ n, CoeffEq CcT
    (cand (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c) (hlTop G m ρ p c h Ccπ)) t₀ t₁ g n
  path : ∀ L ≤ h, ∀ σ : StagePath G L, ∀ g ≤ L, ∀ n, CoeffEq (Ccπ L σ)
    (cand (chainFam (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ))
      (hlTop G m ρ p c h Ccπ)) t₀ t₁ g n

namespace Setting

variable {G : GenStage D hr Dm b j₀} {m : ℕ} {k : ℤ} {A : RealChain} {ρ : ℝ} {p : OddSlot}
  {c : StageCtx D b j₀ G.level p} {t₀ t₁ : ℝ} {h N sX sZ : ℕ}
  {Ccπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)}

theorem goodDat_path (H : Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) {g : ℕ}
    (σ : StagePath G g) (i : Fin g) : ∀ t ∈ Icc t₀ t₁,
      GoodDat (N + 1 + Dm) t (pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ i) :=
  H.goodDat _ _ _

/-- The arising step data are good. -/
theorem goodDat_arise (H : Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) {g : ℕ}
    {cd : Fin g → StepDat} (hA : stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h g cd)
    (i : Fin g) : ∀ t ∈ Icc t₀ t₁, GoodDat (N + 1 + Dm) t (cd i) := by
  obtain ⟨_, σ, rfl⟩ := hA
  exact H.goodDat_path σ i

theorem lift_seq (H : Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) {g : ℕ}
    {cd : Fin g → StepDat} (hA : stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h g cd) :
    IsLiftSequence (stQc G m k A ρ p c h g cd) sX sZ t₀ t₁ N g
      (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ g cd) := by
  classical
  simp only [stQc, stLift, dite_eq_left_of_eq_true (eq_true hA)]
  exact H.hπ g hA.1 _

/-- The top arrays are good at the window times. -/
theorem goodT (H : Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (g : ℕ) (cd : Fin g → StepDat) (k' m' : ℕ) (α : DerivativeWord2 m') :
    GoodField (N + 1 + Dm) (fun X z => hlTop G m ρ p c h Ccπ g cd k' m' α t X z) := by
  classical
  by_cases hA : stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h g cd
  · simp only [hlTop, topOf, hA, ite_true, topArr]
    obtain ⟨_, _, _, _, _, h5, _⟩ := H.lift_seq hA
    have hb := ((h5 g le_rfl k' m' α (Fin.last g) 0 t ht).1).map_clm
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    refine ⟨(hb.contDiff_uncurry H.hsX H.hsZ), fun X n x => ?_⟩
    have := (h5 g le_rfl k' m' α (Fin.last g) 0 t ht).2 X n x
    simp only at this ⊢
    rw [this]
  · simp only [hlTop, topOf, hA, ite_false]
    exact GoodField.zero

/-- **The step hypotheses of a path family.** -/
theorem chainHyp [∀ r, FiniteDimensional ℝ (hr r)]
    (H : Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) (hD2 : 2 ≤ Dm) {L : ℕ} (hL : L ≤ h)
    (σ : StagePath G L) {cd : Fin L → StepDat}
    (hcd : pathDat G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c σ = cd) :
    StepHyp (chainFam cd) (familyLiftData D m k A ρ (pathEdges G σ p c))
      (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ) (stQc G m k A ρ p c h)
      (stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h) sX sZ t₀ t₁ N N L where
  hQ := hcd ▸ hasFamFlux_pathEdges G m k A ρ p c σ
  hab := H.window
  hW := H.windowData
  hQc _ _ hA := StageSetting.qc_flux hA
  hη _ _ := rfl
  hG _ _ := rfl
  hv _ _ := rfl
  hLs _ _ hA := H.lift_seq hA
  hcd _ _ hA := H.goodDat_arise hA
  hdat _ i _ := by subst hcd; exact H.goodDat_path σ _
  hGr := H.metric
  hvr := H.drift
  hD2 := hD2
  hsX := H.hsX
  hsZ := H.hsZ
  hNr := le_rfl
  hArise _ _ _ τ hg := StageSetting.arise_chain (hcd ▸ ⟨hL, σ, rfl⟩) τ hg

/-- **The step hypotheses of the stage.** -/
theorem stageHyp [∀ r, FiniteDimensional ℝ (hr r)]
    (H : Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) (hD2 : 2 ≤ Dm) :
    StepHyp (stageFam G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c)
      (familyLiftData D m k A ρ (G.fam.fiber p c))
      (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ) (stQc G m k A ρ p c h)
      (stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h) sX sZ t₀ t₁ N N h where
  hQ := hasFamFlux_fiber G m k A ρ p c
  hab := H.window
  hW := H.windowData
  hQc _ _ hA := StageSetting.qc_flux hA
  hη _ _ := rfl
  hG _ _ := rfl
  hv _ _ := rfl
  hLs _ _ hA := H.lift_seq hA
  hcd _ _ hA := H.goodDat_arise hA
  hdat v u γ := H.goodDat v u γ
  hGr := H.metric
  hvr := H.drift
  hD2 := hD2
  hsX := H.hsX
  hsZ := H.hsZ
  hNr := le_rfl
  hArise _ _ _ q hg := ⟨hg, stage_walk_path q⟩

/-- The arising chain families satisfy the step hypotheses. -/
theorem chainHyps [∀ r, FiniteDimensional ℝ (hr r)]
    (H : Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) (hD2 : 2 ≤ Dm) :
    ∀ L (cd : Fin L → StepDat), stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h L cd →
      StepHyp (chainFam cd) (stQc G m k A ρ p c h L cd)
        (stLift G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h Ccπ) (stQc G m k A ρ p c h)
        (stArise G (D.cellScaleSq m) (ρ / D.eps (m - 1)) p c h) sX sZ t₀ t₁ N N L := by
  classical
  intro L cd hA
  have := H.chainHyp hD2 hA.1 (Classical.choose hA.2) (Classical.choose_spec hA.2)
  simp only [stQc, dite_eq_left_of_eq_true (eq_true hA)]
  exact this

/-- **The path decomposition of a stage with global path lifts**, for `2 ≤ Dm`. -/
theorem decomposed [∀ r, FiniteDimensional ℝ (hr r)]
    (H : Setting G m k A ρ p c t₀ t₁ h N sX sZ Ccπ) (hD2 : 2 ≤ Dm)
    {CcT : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)}
    (hT : IsLiftSequence (familyLiftData D m k A ρ (G.fam.fiber p c)) sX sZ t₀ t₁ N h CcT) :
    Decomposed G m ρ p c t₀ t₁ h CcT Ccπ where
  stage := decomp (H.stageHyp hD2) (fun L cd hA _ => H.chainHyps hD2 L cd hA) hT
  path L hL σ := decomp (H.chainHyp hD2 hL σ rfl) (fun L cd hA _ => H.chainHyps hD2 L cd hA)
    (H.hπ L hL σ)

end Setting

end AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLDecomp
end
end
end
