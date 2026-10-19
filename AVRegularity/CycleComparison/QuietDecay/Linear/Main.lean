-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CycleComparison.QuietDecay.Lift.QuietMeanFrom

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.QuietDecay

/-! The `ε`-polynomial structure of the source operator with a regularity parameter `r`: for an
input field of regularity `r + D` and edge coefficients that are `C^{r+1}` in the slow variable,
`𝒮_ε Φ` is a polynomial in `ε` of degree `≤ D` with coefficients of regularity `r`. -/

section
open AVRegularity

section Source
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem sourceTerm_epsPoly_r {c : Prop} {r d : ℕ} (hd : 2 ≤ d) (hdD : d ≤ D) (η t : ℝ)
    {u v : ι} (γ : Constituent d (h u) (h v)) (α : DerivativeWord2 (d - 1))
    (hquiet : ∀ X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ z, ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c (r + D) Φ) (k : Fin 2) :
    EpsPoly c (D - 1) (r + 1)
      (fun ε X z => (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)) := by
  have hw : EpsPoly c (0 + (d - 1)) (r + 1) (fun ε => dEpsWord η ε α Φ) :=
    EpsPoly.dEpsWord η α (EpsPoly.const (hΦ.mono (by omega)))
  have hw' : EpsPoly c (D - 1) (r + 1) (fun ε => dEpsWord η ε α Φ) := hw.mono_deg (by omega)
  have hl := hw'.clm (γ.map.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u))
  have hg : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X 0 k) :=
    contDiff_pi.mp (hsm 0) k
  refine EpsPoly.congr (fun ε X z => ?_) (hl.mulX hg)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [hquiet X z 0]

theorem sourceFlux_epsPoly_r {c : Prop} {r : ℕ} (edge : ConstituentEdges D h) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c (r + D) Φ) (k : Fin 2) :
    EpsPoly c (D - 1) (r + 1) (fun ε => sourceFlux edge η ε t Φ k) := by
  refine EpsPoly.of_forall_apply (ι := ι) (h := h)
    (Ψ := fun ε => sourceFlux edge η ε t Φ k) fun v => ?_
  simp only [sourceFlux]
  refine EpsPoly.sum _ fun u _ => EpsPoly.sum _ fun d _ => EpsPoly.list_sum _ fun γ hγ =>
    EpsPoly.sum _ fun α _ => ?_
  have hd := Finset.mem_Icc.mp d.2
  exact sourceTerm_epsPoly_r hd.1 hd.2 η t γ α (hquiet v u d γ hγ α) (hsm v u d γ hγ α) hΦ k

theorem sourceOp_epsPoly_r {c : Prop} {r : ℕ} (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c (r + D) Φ) :
    EpsPoly c D r (fun ε => sourceOp edge η ε t Φ) := by
  have hk : ∀ k : Fin 2, EpsPoly c D r (fun ε => dEps η ε k (sourceFlux edge η ε t Φ k)) :=
    fun k => ((sourceFlux_epsPoly_r edge η t hquiet hsm hΦ k).dEps η k).mono_deg (by omega)
  exact EpsPoly.sum (Finset.univ : Finset (Fin 2))
    (Ψ := fun k ε => dEps η ε k (sourceFlux edge η ε t Φ k)) (fun k _ => hk k)

theorem sourceCoeff_coefField_r {c : Prop} {r : ℕ} (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c (r + D) Φ) (j : ℕ) :
    CoefField c r (sourceCoeff edge η j t Φ) := by
  obtain ⟨P, hP, hz, he⟩ := sourceOp_epsPoly_r edge hD η t hquiet hsm hΦ
  have : sourceCoeff edge η j t Φ = fun X z => if j ≤ D then P j X z else 0 := by
    funext X z
    have hf : (fun ε : ℝ => sourceOp edge η ε t Φ X z) =
        fun ε => ∑ i ∈ Finset.range (D + 1), ε ^ i • P i X z := funext fun ε => he ε X z
    simp only [sourceCoeff, hf, iteratedDeriv_epsPoly]
    by_cases hj : j ≤ D
    · simp [hj, Nat.factorial_ne_zero]
    · simp [hj]
  rw [this]
  by_cases hj : j ≤ D
  · simpa [hj] using hP j
  · simpa [hj] using (CoefField.zero (c := c) (r := r))

end Source
end

/-! Linearity in the test field, part 1: word derivatives, the lift action, the covariant
derivative `D_ε` and its words, all for finite real linear combinations of smooth fields. -/

section
open AVRegularity

section Word
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {κ : Type*}

theorem orderedDerivative_const_smul' (c : ℝ) {j : ℕ} (β : DerivativeWord2 j) {g : Vec 2 → F}
    (hg : ContDiff ℝ (j : ℕ∞) g) :
    orderedDerivative β (fun x => c • g x) = fun x => c • orderedDerivative β g x := by
  have := orderedDerivative_clm_comp (c • ContinuousLinearMap.id ℝ F) β hg
  simpa using this

theorem orderedDerivative_fsum_smul (s : Finset κ) (c : κ → ℝ) {j : ℕ} (β : DerivativeWord2 j)
    {g : κ → Vec 2 → F} (hg : ∀ k ∈ s, ContDiff ℝ (j : ℕ∞) (g k)) :
    orderedDerivative β (fun x => ∑ k ∈ s, c k • g k x) =
      fun x => ∑ k ∈ s, c k • orderedDerivative β (g k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using orderedDerivative_const_zero (F := F) β
  | insert a s ha ih =>
    have h1 : ∀ k ∈ s, ContDiff ℝ (j : ℕ∞) (g k) := fun k hk => hg k (Finset.mem_insert_of_mem hk)
    have h2 : ContDiff ℝ (j : ℕ∞) (g a) := hg a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha]
    rw [orderedDerivative_add β (h2.const_smul (c a))
      (ContDiff.sum fun k hk => (h1 k hk).const_smul (c k)),
      orderedDerivative_const_smul' (c a) β h2, ih h1]

end Word

section Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {κ : Type*}

/-- The lift action is linear in the test field. -/
theorem liftApply_fsum (n : ℕ) (cc : LiftCoeff ι h) (s : Finset κ) (c : κ → ℝ)
    (a : κ → Vec 2 → ∀ i, h i) (ha : ∀ k ∈ s, ContDiff ℝ (n : ℕ∞) (a k)) (t : ℝ) (X z : Vec 2) :
    liftApply n cc (fun _ => fun Y => ∑ k ∈ s, c k • a k Y) t X z =
      ∑ k ∈ s, c k • liftApply n cc (fun _ => a k) t X z := by
  funext v
  have e : ∀ m ∈ Finset.range (n + 1), ∀ (α : DerivativeWord2 m) (u : ι),
      cc m α t X z v u (orderedDerivative α (fun Y => ∑ k ∈ s, c k • a k Y) X u) =
        ∑ k ∈ s, c k • cc m α t X z v u (orderedDerivative α (a k) X u) := by
    intro m hm α u
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [orderedDerivative_fsum_smul s c α fun k hk => (ha k hk).of_le (by exact_mod_cast hm')]
    simp [map_sum, map_smul, Finset.sum_apply]
  simp only [liftApply, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => e m hm α u]
  simp only [Finset.smul_sum]
  symm
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm (s := s)]

end Lift

section DEps
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*}

theorem GoodField.dEps' {r : ℕ} {Ψ : Vec 2 → Vec 2 → E} (hΨ : GoodField (r + 1) Ψ) (η ε : ℝ)
    (i : Fin 2) : GoodField r (dEps η ε i Ψ) :=
  (hΨ.fastPartial i).add ((hΨ.slowPartial i).smul (Real.sqrt η * ε))

theorem dEps_fsum (η ε : ℝ) (i : Fin 2) (s : Finset κ) (c : κ → ℝ) {Φ : κ → Vec 2 → Vec 2 → E}
    (hΦ : ∀ k ∈ s, GoodField 1 (Φ k)) :
    dEps η ε i (fun X z => ∑ k ∈ s, c k • Φ k X z) =
      fun X z => ∑ k ∈ s, c k • dEps η ε i (Φ k) X z := by
  funext X z
  simp only [dEps]
  rw [fastPartial_sum_smul s c Φ hΦ i X z, slowPartial_sum_smul s c Φ hΦ i X z,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_add, smul_comm (c k)]

theorem foldl_dEps_fsum (η ε : ℝ) (s : Finset κ) (c : κ → ℝ) (l : List (Fin 2)) :
    ∀ (Φ : κ → Vec 2 → Vec 2 → E), (∀ k ∈ s, GoodField l.length (Φ k)) →
      l.foldl (fun Ψ' i => dEps η ε i Ψ') (fun X z => ∑ k ∈ s, c k • Φ k X z) =
        fun X z => ∑ k ∈ s, c k • l.foldl (fun Ψ' i => dEps η ε i Ψ') (Φ k) X z := by
  induction l with
  | nil => intro Φ _; rfl
  | cons i l ih =>
    intro Φ hΦ
    simp only [List.foldl_cons]
    rw [dEps_fsum η ε i s c fun k hk => (hΦ k hk).mono (by simp)]
    exact ih (fun k => dEps η ε i (Φ k)) fun k hk => GoodField.dEps' (hΦ k hk) η ε i

theorem dEpsWord_fsum (η ε : ℝ) (s : Finset κ) (c : κ → ℝ) {m : ℕ} (α : DerivativeWord2 m)
    {Φ : κ → Vec 2 → Vec 2 → E} (hΦ : ∀ k ∈ s, GoodField m (Φ k)) :
    dEpsWord η ε α (fun X z => ∑ k ∈ s, c k • Φ k X z) =
      fun X z => ∑ k ∈ s, c k • dEpsWord η ε α (Φ k) X z :=
  foldl_dEps_fsum η ε s c (List.ofFn α) Φ fun k hk => by simpa using hΦ k hk

theorem epsPoly_goodField {c : Prop} {q r : ℕ} {Ψ : ℝ → Vec 2 → Vec 2 → E}
    (h : EpsPoly c q r Ψ) (ε : ℝ) : GoodField r (Ψ ε) := by
  obtain ⟨P, hP, _, he⟩ := h
  have : Ψ ε = fun X z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z :=
    funext fun X => funext fun z => he ε X z
  rw [this]
  exact GoodField.sum _ fun i _ => (hP i).1.smul _

end DEps
end

/-! Linearity in the test field, part 2: the source flux, the source operator `𝒮_ε` (for each
`ε`) and its Taylor coefficients `𝒮_j`, for finite real linear combinations of `C^D` periodic
fields at a quiet time. -/

section
open AVRegularity

theorem list_sum_map_fsum {E κ γ : Type*} [AddCommGroup E] [Module ℝ E] (s : Finset κ)
    (c : κ → ℝ) (g : γ → κ → E) (L : List γ) :
    (L.map fun x => ∑ j ∈ s, c j • g x j).sum = ∑ j ∈ s, c j • (L.map fun x => g x j).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib, smul_add]

theorem fsum_swap {E κ γ : Type*} [AddCommGroup E] [Module ℝ E] (s : Finset κ) (c : κ → ℝ)
    (A : Finset γ) (g : γ → κ → E) :
    ∑ x ∈ A, ∑ j ∈ s, c j • g x j = ∑ j ∈ s, c j • ∑ x ∈ A, g x j := by
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

section Source
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {κ : Type*}

theorem sourceFlux_fsum (edge : ConstituentEdges D h) (η ε t : ℝ) (s : Finset κ) (c : κ → ℝ)
    {Φ : κ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : ∀ k ∈ s, GoodField D (Φ k)) (k' : Fin 2) :
    sourceFlux edge η ε t (fun X z => ∑ j ∈ s, c j • Φ j X z) k' =
      fun X z => ∑ j ∈ s, c j • sourceFlux edge η ε t (Φ j) k' X z := by
  have key : ∀ d : Finset.Icc 2 D, ∀ α : DerivativeWord2 (d.1 - 1),
      dEpsWord η ε α (fun X z => ∑ j ∈ s, c j • Φ j X z) =
        fun X z => ∑ j ∈ s, c j • dEpsWord η ε α (Φ j) X z := fun d α =>
    dEpsWord_fsum η ε s c α fun k hk => (hΦ k hk).mono (by
      have := (Finset.mem_Icc.mp d.2).2; omega)
  funext X z v
  simp only [sourceFlux, key]
  have hterm : ∀ (u : ι) (d : Finset.Icc 2 D) (γ : Constituent d.1 (h u) (h v)),
      (∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α t X z k') •
        γ.map ((∑ j ∈ s, c j • dEpsWord η ε α (Φ j) X z) u)) =
      ∑ j ∈ s, c j • ∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α t X z k') •
        γ.map (dEpsWord η ε α (Φ j) X z u) := by
    intro u d γ
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
    rw [smul_comm]
  simp only [hterm, list_sum_map_fsum]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sourceFlux, Finset.smul_sum]

end Source

section SourceOp
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {κ : Type*}

/-- The `ε`-polynomial form of the source operator on `C^D` periodic fields at a quiet time. -/
theorem sourceOp_epsPoly_good (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : GoodField D Φ) :
    EpsPoly False D 0 (fun ε => sourceOp edge η ε t Φ) :=
  sourceOp_epsPoly_r (r := 0) edge hD η t hquiet (fun v u d γ hγ α z => by
    simpa using hsm v u d γ hγ α z) (⟨by simpa using hΦ, fun hf => hf.elim⟩)

theorem sourceFlux_goodField (edge : ConstituentEdges D h) (η ε t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : GoodField D Φ) (k : Fin 2) :
    GoodField 1 (sourceFlux edge η ε t Φ k) := by
  have h0 : EpsPoly False (D - 1) (0 + 1) (fun ε => sourceFlux edge η ε t Φ k) :=
    sourceFlux_epsPoly_r (r := 0) (c := False) edge η t hquiet (fun v u d γ hγ α z => by
      simpa using hsm v u d γ hγ α z) (⟨by simpa using hΦ, fun hf => hf.elim⟩) k
  simpa using epsPoly_goodField h0 ε

/-- The source operator is linear in the field, for each `ε`. -/
theorem sourceOp_fsum (edge : ConstituentEdges D h) (η ε t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    (s : Finset κ) (c : κ → ℝ) {Φ : κ → Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : ∀ k ∈ s, GoodField D (Φ k)) :
    sourceOp edge η ε t (fun X z => ∑ j ∈ s, c j • Φ j X z) =
      fun X z => ∑ j ∈ s, c j • sourceOp edge η ε t (Φ j) X z := by
  funext X z
  have e1 : ∀ k' : Fin 2, sourceFlux edge η ε t (fun X z => ∑ j ∈ s, c j • Φ j X z) k' =
      fun X z => ∑ j ∈ s, c j • sourceFlux edge η ε t (Φ j) k' X z := fun k' =>
    sourceFlux_fsum edge η ε t s c hΦ k'
  simp only [sourceOp, e1]
  simp only [dEps_fsum η ε _ s c fun j hj => sourceFlux_goodField edge η ε t hquiet hsm (hΦ j hj) _]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

theorem sourceCoeff_fsum (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    (s : Finset κ) (c : κ → ℝ) {Φ : κ → Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : ∀ k ∈ s, GoodField D (Φ k)) (m : ℕ) (X z : Vec 2) :
    sourceCoeff edge η m t (fun X z => ∑ j ∈ s, c j • Φ j X z) X z =
      ∑ j ∈ s, c j • sourceCoeff edge η m t (Φ j) X z := by
  have hf : (fun ε : ℝ => sourceOp edge η ε t (fun X z => ∑ j ∈ s, c j • Φ j X z) X z) =
      fun ε => ∑ j ∈ s, c j • sourceOp edge η ε t (Φ j) X z := by
    funext ε
    exact congrFun (congrFun (sourceOp_fsum edge η ε t hquiet hsm s c hΦ) X) z
  have hcd : ∀ j ∈ s, ContDiffAt ℝ (m : WithTop ℕ∞)
      (fun ε : ℝ => c j • sourceOp edge η ε t (Φ j) X z) 0 := by
    intro j hj
    obtain ⟨P, _, _, he⟩ := sourceOp_epsPoly_good edge hD η t hquiet hsm (hΦ j hj)
    have : (fun ε : ℝ => c j • sourceOp edge η ε t (Φ j) X z) =
        fun ε => c j • ∑ i ∈ Finset.range (D + 1), ε ^ i • P i X z := funext fun ε =>
      congrArg (fun w => c j • w) (he ε X z)
    rw [this]
    exact (ContDiff.const_smul (c j) (ContDiff.sum fun i _ =>
      (contDiff_id.pow i).smul contDiff_const)).contDiffAt
  simp only [sourceCoeff, hf]
  rw [iteratedDeriv_fun_sum hcd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedDeriv_fun_const_smul_field (c j) (fun ε : ℝ => sourceOp edge η ε t (Φ j) X z), smul_comm]

end SourceOp
end

/-! Linearity in the test field, part 3: the cell operators `ℬ₁`, `ℬ₂` on `C^2` periodic fields,
and the regularity of `ℬ₂` on slow-only fields. -/

section
open AVRegularity

section Cell
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*}

theorem cellB1_fsum (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j)) (s : Finset κ) (c : κ → ℝ)
    {Φ : κ → Vec 2 → Vec 2 → E} (hΦ : ∀ k ∈ s, GoodField 2 (Φ k)) (X z : Vec 2) :
    cellB1 η G v t (fun X z => ∑ k ∈ s, c k • Φ k X z) X z =
      ∑ k ∈ s, c k • cellB1 η G v t (Φ k) X z := by
  have g1 : ∀ k ∈ s, GoodField 1 (Φ k) := fun k hk => (hΦ k hk).mono (by norm_num)
  have gs : ∀ j : Fin 2, ∀ k ∈ s, GoodField 1 (slowPartial j (Φ k)) := fun j k hk =>
    GoodField.slowPartial (r := 1) (hΦ k hk) j
  have gf : ∀ i j : Fin 2, ∀ k ∈ s, GoodField 1 (fun X z => G t X i j • fastPartial j (Φ k) X z) :=
    fun i j k hk => (GoodField.fastPartial (r := 1) (hΦ k hk) j).mulX (hG i j)
  have T1 : ∀ k' : Fin 2, slowPartial k' (fun X z => ∑ k ∈ s, c k • Φ k X z) X z =
      ∑ k ∈ s, c k • slowPartial k' (Φ k) X z := fun k' =>
    slowPartial_sum_smul s c Φ g1 k' X z
  have T2 : ∀ i j : Fin 2, fastPartial i (slowPartial j (fun X z => ∑ k ∈ s, c k • Φ k X z)) X z =
      ∑ k ∈ s, c k • fastPartial i (slowPartial j (Φ k)) X z := by
    intro i j
    have e : slowPartial j (fun X z => ∑ k ∈ s, c k • Φ k X z) =
        fun X z => ∑ k ∈ s, c k • slowPartial j (Φ k) X z :=
      funext fun X => funext fun z => slowPartial_sum_smul s c Φ g1 j X z
    rw [e]
    exact fastPartial_sum_smul s c (fun k => slowPartial j (Φ k)) (gs j) i X z
  have T3 : ∀ i j : Fin 2, slowPartial i (fun X' z' => G t X' i j •
      fastPartial j (fun X z => ∑ k ∈ s, c k • Φ k X z) X' z') X z =
      ∑ k ∈ s, c k • slowPartial i (fun X' z' => G t X' i j • fastPartial j (Φ k) X' z') X z := by
    intro i j
    have e : (fun X' z' => G t X' i j • fastPartial j (fun X z => ∑ k ∈ s, c k • Φ k X z) X' z') =
        fun X' z' => ∑ k ∈ s, c k • (G t X' i j • fastPartial j (Φ k) X' z') := by
      funext X' z'
      rw [fastPartial_sum_smul s c Φ g1 j X' z', Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [e]
    exact slowPartial_sum_smul s c (fun k X z => G t X i j • fastPartial j (Φ k) X z) (gf i j) i X z
  simp only [cellB1, T1, T2, T3]
  simp only [Finset.smul_sum, smul_sub, smul_add]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have c1 : ∀ (f : Fin 2 → κ → E), ∑ a, ∑ k ∈ s, f a k = ∑ k ∈ s, ∑ a, f a k := fun f =>
    Finset.sum_comm
  have c2 : ∀ (f : Fin 2 → Fin 2 → κ → E), ∑ a, ∑ b, ∑ k ∈ s, f a b k =
      ∑ k ∈ s, ∑ a, ∑ b, f a b k := fun f =>
    (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  rw [c1, c2, c2]
  refine congrArg₂ (· - ·) ?_ (congrArg₂ (· + ·) ?_ ?_)
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by module
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by module
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by module

theorem cellB2_fsum (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j)) (s : Finset κ) (c : κ → ℝ)
    {Φ : κ → Vec 2 → Vec 2 → E} (hΦ : ∀ k ∈ s, GoodField 2 (Φ k)) (X z : Vec 2) :
    cellB2 η G t (fun X z => ∑ k ∈ s, c k • Φ k X z) X z =
      ∑ k ∈ s, c k • cellB2 η G t (Φ k) X z := by
  have g1 : ∀ k ∈ s, GoodField 1 (Φ k) := fun k hk => (hΦ k hk).mono (by norm_num)
  have gf : ∀ i j : Fin 2, ∀ k ∈ s, GoodField 1 (fun X z => G t X i j • slowPartial j (Φ k) X z) :=
    fun i j k hk => (GoodField.slowPartial (r := 1) (hΦ k hk) j).mulX (hG i j)
  have T3 : ∀ i j : Fin 2, slowPartial i (fun X' z' => G t X' i j •
      slowPartial j (fun X z => ∑ k ∈ s, c k • Φ k X z) X' z') X z =
      ∑ k ∈ s, c k • slowPartial i (fun X' z' => G t X' i j • slowPartial j (Φ k) X' z') X z := by
    intro i j
    have e : (fun X' z' => G t X' i j • slowPartial j (fun X z => ∑ k ∈ s, c k • Φ k X z) X' z') =
        fun X' z' => ∑ k ∈ s, c k • (G t X' i j • slowPartial j (Φ k) X' z') := by
      funext X' z'
      rw [slowPartial_sum_smul s c Φ g1 j X' z', Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [e]
    exact slowPartial_sum_smul s c (fun k X z => G t X i j • slowPartial j (Φ k) X z) (gf i j) i X z
  simp only [cellB2, T3]
  simp only [Finset.smul_sum]
  have c2 : ∀ (f : Fin 2 → Fin 2 → κ → E), ∑ a, ∑ b, ∑ k ∈ s, f a b k =
      ∑ k ∈ s, ∑ a, ∑ b, f a b k := fun f =>
    (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  rw [c2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by
    rw [smul_neg, neg_inj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by module

/-- `ℬ₂` maps `C^{r+2}` periodic fields to `C^r` periodic fields, for a `C^{r+1}` metric. -/
theorem cellB2_goodField (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) {r : ℕ}
    (hG : ∀ i j, ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => G t X i j)) {Φ : Vec 2 → Vec 2 → E}
    (hΦ : GoodField (r + 2) Φ) : GoodField r (cellB2 η G t Φ) := by
  have hF : ∀ i j : Fin 2, GoodField r
      (slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z')) := fun i j =>
    GoodField.slowPartial (r := r) ((GoodField.slowPartial (r := r + 1) hΦ j).mulX (hG i j)) i
  exact ((GoodField.sum (Finset.univ : Finset (Fin 2)) fun i _ =>
    GoodField.sum (Finset.univ : Finset (Fin 2)) fun j _ => hF i j).smul η).neg

end Cell
end

/-! Linearity of the quiet cell source `quietSource` in the test field, for finite real linear
combinations of `C^∞` test fields. -/

section
open AVRegularity

section Main
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {κ : Type*}

/-- The regularity premises of the linearity of `quietSource` in the test field, at the time `t`,
the amplitude index `hh` and the order `n`. -/
structure QuietLinearFacts (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (t : ℝ)
    (hh n : ℕ) : Prop where
  D_ge : 2 ≤ D
  /-- The lift coefficients are box smooth of orders `(D, D)` and periodic in `z`. -/
  coeff : ∀ p ≤ hh, ∀ j m α v u, IsBoxSmooth D D (fun X z => Cc p j m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => Cc p j m α t X z v u)
  G_smooth : ∀ i j, ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (fun X => Q.G t X i j)
  edge_quiet : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z'
  edge_smooth : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
    ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X z)

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {t : ℝ} {hh n : ℕ}

theorem slow_goodField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : Vec 2 → E}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (r : ℕ) : GoodField r (fun X (_ : Vec 2) => b X) :=
  ⟨(hb.of_le (by exact_mod_cast le_top)).comp contDiff_fst, fun _ _ _ => rfl⟩

theorem GoodField.contDiff_zero_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} {F : Vec 2 → Vec 2 → E} (hF : GoodField r F) : ContDiff ℝ (r : ℕ∞) (fun X => F X 0) :=
  hF.1.comp (contDiff_id.prodMk contDiff_const)

theorem QuietLinearFacts.quietMeanOp_contDiff (hf : QuietLinearFacts Q Cc t hh n)
    {b : Vec 2 → ∀ i, h i} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p2 n' r : ℕ) (hr : r ≤ n) :
    ContDiff ℝ (r : ℕ∞) (fun X' => quietMeanOp Q b p2 n' t X') := by
  have hr1 : (((r + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast Nat.succ_le_succ hr
  unfold quietMeanOp
  by_cases h0 : p2 = 0
  · simp only [h0, ↓reduceIte]
    by_cases h2 : n' = 2
    · simp only [h2, ↓reduceIte]
      exact GoodField.contDiff_zero_slice (cellB2_goodField Q.η Q.G t (r := r)
        (fun i j => (hf.G_smooth i j).of_le hr1) (slow_goodField hb (r + 2)))
    · simp only [h2, ↓reduceIte]; exact contDiff_const
  · simp only [h0, ↓reduceIte]
    by_cases h1 : p2 = 1
    · simp only [h1, ↓reduceIte]
      have := sourceCoeff_coefField_r (c := False) (r := r) Q.edge (by have := hf.D_ge; omega) Q.η t
        hf.edge_quiet (fun v u d γ hγ α z => (hf.edge_smooth v u d γ hγ α z).of_le hr1)
        (Φ := fun X (_ : Vec 2) => b X) ⟨slow_goodField hb (r + D), fun hf => hf.elim⟩ n'
      exact (GoodField.contDiff_zero_slice this.1).neg
    · simp only [h1, ↓reduceIte]; exact contDiff_const

theorem QuietLinearFacts.quietMeanOp_fsum (hf : QuietLinearFacts Q Cc t hh n) (s : Finset κ)
    (c : κ → ℝ) {b : κ → Vec 2 → ∀ i, h i} (hb : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (b k)) (p2 n' : ℕ)
    (X' : Vec 2) :
    quietMeanOp Q (fun Y => ∑ k ∈ s, c k • b k Y) p2 n' t X' =
      ∑ k ∈ s, c k • quietMeanOp Q (b k) p2 n' t X' := by
  have hD1 : 1 ≤ D := by have := hf.D_ge; omega
  have hG1 : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j) := fun i j =>
    (hf.G_smooth i j).of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hsm1 : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z) := fun v u d γ hγ α z =>
    (hf.edge_smooth v u d γ hγ α z).of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  unfold quietMeanOp
  by_cases h0 : p2 = 0
  · simp only [h0, ↓reduceIte]
    by_cases h2 : n' = 2
    · simp only [h2, ↓reduceIte]
      exact cellB2_fsum Q.η Q.G t hG1 s c (Φ := fun k X (_ : Vec 2) => b k X)
        (fun k _ => (slow_goodField (hb k) 2)) X' 0
    · simp [h2]
  · simp only [h0, ↓reduceIte]
    by_cases h1 : p2 = 1
    · simp only [h1, ↓reduceIte]
      rw [sourceCoeff_fsum Q.edge hD1 Q.η t hf.edge_quiet hsm1 s c
        (Φ := fun k X (_ : Vec 2) => b k X) (fun k _ => slow_goodField (hb k) D) n' X' 0]
      simp [Finset.sum_neg_distrib]
    · simp [h1]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem liftApply_congr_time (n : ℕ) (cc : LiftCoeff ι h) {a a' : ℝ → Vec 2 → ∀ i, h i} {t : ℝ}
    (ha : a t = a' t) : liftApply n cc a t = liftApply n cc a' t := by
  unfold liftApply
  rw [ha]

/-- **Linearity of the quiet cell source in the test field**: for finite real linear combinations
of `C^∞` test fields. -/
theorem QuietLinearFacts.quietSource_fsum (hf : QuietLinearFacts Q Cc t hh n) (s : Finset κ)
    (c : κ → ℝ) {b : κ → Vec 2 → ∀ i, h i} (hb : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (b k)) (X z : Vec 2) :
    quietSource Q Cc (fun Y => ∑ k ∈ s, c k • b k Y) hh n t X z =
      ∑ k ∈ s, c k • quietSource Q Cc (b k) hh n t X z := by
  have hD2 := hf.D_ge
  have hG1 : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j) := fun i j =>
    (hf.G_smooth i j).of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hsm1 : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z) := fun v u d γ hγ α z =>
    (hf.edge_smooth v u d γ hγ α z).of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have LA : ∀ p ≤ hh, ∀ m, liftApply m (Cc p m) (fun _ => fun Y => ∑ k ∈ s, c k • b k Y) t =
      fun X z => ∑ k ∈ s, c k • liftApply m (Cc p m) (fun _ => b k) t X z := fun p _ m =>
    funext fun X => funext fun z =>
      liftApply_fsum m (Cc p m) s c b (fun k _ => (hb k).of_le (by exact_mod_cast le_top)) t X z
  have LG : ∀ p ≤ hh, ∀ m, ∀ k, GoodField D (liftApply m (Cc p m) (fun _ => b k) t) :=
    fun p hp m k => liftApply_goodField (Cc p m) (b k) (hb k) m D t (hf.coeff p hp m)
  have E1 : (if 2 ≤ n then cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1))
        (fun _ => fun Y => ∑ k ∈ s, c k • b k Y) t) X z else 0) =
      ∑ k ∈ s, c k • (if 2 ≤ n then cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1))
        (fun _ => b k) t) X z else 0) := by
    by_cases h2 : 2 ≤ n
    · simp only [h2, ↓reduceIte]
      rw [LA hh le_rfl (n - 1)]
      exact cellB1_fsum Q.η Q.G Q.v t hG1 s c (fun k _ => (LG hh le_rfl (n - 1) k).mono hD2) X z
    · simp [h2]
  have E2 : (if 3 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2))
        (fun _ => fun Y => ∑ k ∈ s, c k • b k Y) t) X z else 0) =
      ∑ k ∈ s, c k • (if 3 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2))
        (fun _ => b k) t) X z else 0) := by
    by_cases h3 : 3 ≤ n
    · simp only [h3, ↓reduceIte]
      rw [LA hh le_rfl (n - 2)]
      exact cellB2_fsum Q.η Q.G t hG1 s c (fun k _ => (LG hh le_rfl (n - 2) k).mono hD2) X z
    · simp [h3]
  have E3 : (if hh = 0 then 0 else ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j))
          (fun _ => fun Y => ∑ k ∈ s, c k • b k Y) t) X z) =
      ∑ k ∈ s, c k • (if hh = 0 then 0 else ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j))
          (fun _ => b k) t) X z) := by
    by_cases hh0 : hh = 0
    · simp [hh0]
    · simp only [hh0, ↓reduceIte]
      have hp : hh - 1 ≤ hh := Nat.sub_le _ _
      have e : ∀ j ∈ (Finset.range (min D n + 1)).filter (· < n),
          sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j))
            (fun _ => fun Y => ∑ k ∈ s, c k • b k Y) t) X z =
          ∑ k ∈ s, c k • sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j))
            (fun _ => b k) t) X z := by
        intro j _
        rw [LA (hh - 1) hp (n - j)]
        exact sourceCoeff_fsum Q.edge (by omega) Q.η t hf.edge_quiet hsm1 s c
          (fun k _ => LG (hh - 1) hp (n - j) k) j X z
      rw [Finset.sum_congr rfl e]
      exact fsum_swap s c _ _
  have E4 : ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (Cc p.1 j) (fun s' X' => quietMeanOp Q (fun Y => ∑ k ∈ s, c k • b k Y)
          p.2 (n - j) s' X') t X z =
      ∑ k ∈ s, c k • ∑ j ∈ Finset.Icc 1 (n - 2),
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftApply j (Cc p.1 j) (fun s' X' => quietMeanOp Q (b k) p.2 (n - j) s' X') t X z := by
    have e : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (Cc p.1 j) (fun s' X' => quietMeanOp Q (fun Y => ∑ k ∈ s, c k • b k Y)
          p.2 (n - j) s' X') t X z =
        ∑ k ∈ s, c k • liftApply j (Cc p.1 j) (fun s' X' => quietMeanOp Q (b k) p.2 (n - j) s' X')
          t X z := by
      intro j hj p _
      have hjn : j ≤ n := by have := (Finset.mem_Icc.mp hj).2; omega
      rw [liftApply_congr_time j (Cc p.1 j) (a' := fun _ => fun Y => ∑ k ∈ s,
        c k • quietMeanOp Q (b k) p.2 (n - j) t Y)
        (funext fun Y => hf.quietMeanOp_fsum s c hb p.2 (n - j) Y)]
      rw [liftApply_fsum j (Cc p.1 j) s c (fun k Y => quietMeanOp Q (b k) p.2 (n - j) t Y)
        (fun k _ => hf.quietMeanOp_contDiff (hb k) p.2 (n - j) j hjn) t X z]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun w => c k • w) (congrFun (congrFun (liftApply_congr_time j (Cc p.1 j)
        (a := fun _ => fun Y => quietMeanOp Q (b k) p.2 (n - j) t Y)
        (a' := fun s' X' => quietMeanOp Q (b k) p.2 (n - j) s' X') (t := t) rfl) X) z)
    rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl (e j hj)]
    rw [Finset.sum_congr rfl fun j _ => fsum_swap s c _ _]
    exact fsum_swap s c _ _
  simp only [quietSource]
  rw [E1, E2, E3, E4]
  simp only [Finset.smul_sum, smul_sub, smul_add, smul_neg, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem quietSource_sum (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) {κ : Type*}
    (s : Finset κ) (c : κ → ℝ) (b : κ → Vec 2 → ∀ i, h i) (hb : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (b k))
    (hh n : ℕ) (t : ℝ) (hf : QuietLinearFacts Q Cc t hh n) (X z : Vec 2) :
    quietSource Q Cc (fun Y => ∑ k ∈ s, c k • b k Y) hh n t X z =
      ∑ k ∈ s, c k • quietSource Q Cc (b k) hh n t X z :=
  hf.quietSource_fsum s c hb X z

end Main
end

end AVRegularity.QuietDecay
end
