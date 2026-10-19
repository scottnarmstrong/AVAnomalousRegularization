-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Carrier
public import AVRegularity.Sobolev.Norms
import AVRegularity.Analysis.Factorial.Drift
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.Sobolev

/-! Periodic `H¹` data and order-one torus jets agree. -/

section
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin

/-- Raw periodic value and derivative data match one order-one torus jet in `L²`. -/
def HasTorusH1Classes (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2) : Prop :=
  AVenhance.IsZ2Periodic f ∧ AVenhance.IsZ2Periodic Df ∧
    ∃ hf : MemL2On AVenhance.unitCube f,
      ∃ hDf : GradMemL2On AVenhance.unitCube Df,
        ∃ w : TorusHk 1 ℝ,
          w.val (valueIndex2 1) = hf.toLp f ∧
            ∀ i : Fin 2,
              w.val (nextIndex2 (⟨0, by omega⟩ : Fin 1) Fin.elim0 i) =
                (hDf i).toLp (fun x => Df x i)

/-- The order-one raw jet associated with a value and its two directional derivatives. -/
def firstJet (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2) : RawJet2 1 ℝ :=
  fun a x =>
    if h : a.1 = (0 : Fin 2) then f x
    else Df x (a.2 ⟨0, Nat.pos_of_ne_zero (fun hv => h (Fin.ext hv))⟩)

/-- The value component of `firstJet` is the given function. -/
theorem firstJet_value (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2) :
    firstJet f Df (valueIndex2 1) = f := by
  funext x
  simp [firstJet, valueIndex2, valueIndex]

/-- The order-one component of `firstJet` is the requested coordinate derivative. -/
theorem firstJet_derivative (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2) (i : Fin 2) :
    firstJet f Df (nextIndex2 (⟨0, by omega⟩ : Fin 1) Fin.elim0 i) = fun x => Df x i := by
  have hneq : (nextIndex2 (⟨0, by omega⟩ : Fin 1) Fin.elim0 i).1 ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [nextIndex2, nextIndex] at hv
  have hcoord : (nextIndex2 (⟨0, by omega⟩ : Fin 1) Fin.elim0 i).2
      (⟨0, by omega⟩ : Fin 1) = i := by
    change (Fin.snoc (n := 0) (α := fun _ : Fin 1 => Fin 2)
      (fun z : Fin 0 => Fin.elim0 z) i) (⟨0, by omega⟩ : Fin 1) = i
    rw [show (⟨0, by omega⟩ : Fin 1) = Fin.last 0 by
      apply Fin.ext
      rfl]
    exact Fin.snoc_last (n := 0) (α := fun _ : Fin 1 => Fin 2) i
      (fun z : Fin 0 => Fin.elim0 z)
  funext x
  simp only [firstJet, dite_eq_right hneq]
  exact congrArg (Df x) hcoord

/-- Coordinatewise `L²` hypotheses give an ordered `L²` first jet. -/
theorem firstJet_memL2 (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2)
    (hf : MemL2On AVenhance.unitCube f) (hDf : GradMemL2On AVenhance.unitCube Df) :
    JetMemL2On AVenhance.unitCube (firstJet f Df) := by
  intro a
  rcases a with ⟨j, w⟩
  have hjcases : j.val = 0 ∨ j.val = 1 := by omega
  rcases hjcases with hj | hj
  · have hj' : j = 0 := Fin.ext hj
    subst j
    have ha : (⟨0, w⟩ : JetIndex2 1) = valueIndex2 1 := by
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext z
        exact Fin.elim0 z
    rw [ha, firstJet_value]
    exact hf
  · have hj' : j = 1 := Fin.ext hj
    subst j
    let i : Fin 2 := w ⟨0, by omega⟩
    have hcoord : (nextIndex2 (⟨0, by omega⟩ : Fin 1) Fin.elim0 i).2
        (⟨0, by omega⟩ : Fin 1) = i := by
      change (Fin.snoc (n := 0) (α := fun _ : Fin 1 => Fin 2)
        (fun z : Fin 0 => Fin.elim0 z) i) (⟨0, by omega⟩ : Fin 1) = i
      rw [show (⟨0, by omega⟩ : Fin 1) = Fin.last 0 by
        apply Fin.ext
        rfl]
      exact Fin.snoc_last (n := 0) (α := fun _ : Fin 1 => Fin 2) i
        (fun z : Fin 0 => Fin.elim0 z)
    have ha : (⟨1, w⟩ : JetIndex2 1) =
        nextIndex2 (⟨0, by omega⟩ : Fin 1) Fin.elim0 i := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · apply heq_of_eq
        funext z
        have hz : z = (⟨0, by omega⟩ : Fin 1) := by
          apply Fin.ext
          omega
        subst z
        change i =
          (nextIndex2 (⟨0, by omega⟩ : Fin 1) Fin.elim0 i).2
            (⟨0, by omega⟩ : Fin 1)
        exact hcoord.symm
    rw [ha, firstJet_derivative]
    exact hDf i

/-- Periodicity of a value and vector field gives periodicity of the whole first jet. -/
theorem firstJet_periodic (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2)
    (hf : AVenhance.IsZ2Periodic f) (hDf : AVenhance.IsZ2Periodic Df) :
    ∀ a, AVenhance.IsZ2Periodic (firstJet f Df a) := by
  intro a n x
  rcases a with ⟨j, w⟩
  fin_cases j
  · simpa [firstJet] using hf n x
  · simpa [firstJet] using congrArg (fun v : Vec 2 => v (w 0)) (hDf n x)

private theorem weakPartialDerivOn_mul_left {U : Set (Vec 2)} (c : ℝ) {i : Fin 2}
    {f g : Vec 2 → ℝ} (h : HasWeakPartialDerivOn U i f g) :
    HasWeakPartialDerivOn U i (fun x => c * f x) (fun x => c * g x) := by
  intro φ hφ hc hs
  calc
    (∫ x in U, (c * f x) * (fderiv ℝ φ x) (basisVec i) ∂volume) =
        c * ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
      calc
        (∫ x in U, (c * f x) * (fderiv ℝ φ x) (basisVec i) ∂volume) =
            ∫ x in U, c * (f x * (fderiv ℝ φ x) (basisVec i)) ∂volume := by
          congr 1
          funext x
          ring
        _ = c * ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
          rw [integral_const_mul]
    _ = c * -(∫ x in U, g x * φ x ∂volume) := by rw [h φ hφ hc hs]
    _ = -(∫ x in U, (c * g x) * φ x ∂volume) := by
      calc
        c * -(∫ x in U, g x * φ x ∂volume) =
            -(c * ∫ x in U, g x * φ x ∂volume) := by ring
        _ = -(∫ x in U, c * (g x * φ x) ∂volume) := by
          rw [integral_const_mul]
        _ = -(∫ x in U, (c * g x) * φ x ∂volume) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          ring

/-- The scalar weak gradient (`HasWeakGradientOn`) gives all scalar-tested first-jet identities. -/
theorem firstJet_hasWeakJet (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2)
    (hweak : HasWeakGradientOn Set.univ f Df) :
    HasOrderedWeakJetOn Set.univ (firstJet f Df) := by
  intro j w i e
  have hj : j = 0 := Fin.ext (by omega)
  subst j
  have hw : w = Fin.elim0 := by funext a; exact Fin.elim0 a
  subst w
  have hder : HasWeakPartialDerivOn Set.univ i
      (fun x => e * firstJet f Df (valueIndex2 1) x)
      (fun x => e * firstJet f Df (nextIndex2 (⟨0, by omega⟩ : Fin 1) Fin.elim0 i) x) :=
    weakPartialDerivOn_mul_left e (hweak i)
  simpa [firstJet_value, firstJet_derivative, lowerIndex2, lowerIndex,
    nextIndex2, nextIndex, valueIndex2, valueIndex, Real.inner_apply, mul_comm] using hder
end

/-! Raw and Hilbert realizations of plane weak Sobolev jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {U : Set (Vec 2)} {K : ℕ}

/-- The continuous linear map used to read the value test in a jet constraint. -/
def testVector (φ : WeakTest U) (e : E) : ComponentL2 (volume.restrict U) E :=
  ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e).compLpL
    2 (volume.restrict U)) (φ.memL2.toLp φ.toFun)

/-- The continuous linear map used to read a differentiated test. -/
def partialTestVector (φ : WeakTest U) (i : Fin 2) (e : E) :
    ComponentL2 (volume.restrict U) E :=
  ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e).compLpL
    2 (volume.restrict U)) ((φ.coordDeriv_memL2 i).toLp (φ.coordDeriv i))

omit [BorelSpace E] [CompleteSpace E] in
/-- The vector-valued scalar test has the expected almost-everywhere representative. -/
theorem testVector_ae (φ : WeakTest U) (e : E) :
    testVector φ e =ᵐ[volume.restrict U] fun x => φ.toFun x • e := by
  have ht := ContinuousLinearMap.coeFn_compLpL
    (p := 2) (μ := volume.restrict U)
    (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e)
    (f := φ.memL2.toLp φ.toFun)
  filter_upwards [ht, φ.memL2.coeFn_toLp] with x hx hφ
  simpa [testVector, hφ] using hx

omit [BorelSpace E] [CompleteSpace E] in
/-- The derivative test has the expected almost-everywhere representative. -/
theorem partialTestVector_ae (φ : WeakTest U) (i : Fin 2) (e : E) :
    partialTestVector φ i e =ᵐ[volume.restrict U] fun x => φ.coordDeriv i x • e := by
  have ht := ContinuousLinearMap.coeFn_compLpL
    (p := 2) (μ := volume.restrict U)
    (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e)
    (f := (φ.coordDeriv_memL2 i).toLp (φ.coordDeriv i))
  filter_upwards [ht, (φ.coordDeriv_memL2 i).coeFn_toLp] with x hx hφ
  simpa [partialTestVector, hφ] using hx

omit [BorelSpace E] in
/-- Unfold a weak constraint as its two scalar integration-by-parts terms. -/
theorem weakJetConstraint_apply (D : JetL2 (volume.restrict U) K E) (j : Fin K)
    (w : DerivativeWord2 j.val) (i : Fin 2) (φ : WeakTest U) (e : E) :
    weakJetConstraint j w i φ e D =
      (∫ x in U, inner ℝ e (D (lowerIndex2 j w) x) * φ.coordDeriv i x ∂volume) +
      (∫ x in U, inner ℝ e (D (nextIndex2 j w i) x) * φ.toFun x ∂volume) := by
  change inner ℝ (partialTestVector φ i e) (D (lowerIndex2 j w)) +
      inner ℝ (testVector φ e) (D (nextIndex2 j w i)) = _
  rw [L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [partialTestVector_ae φ i e] with x hx
    simp [hx, real_inner_smul_left, mul_comm]
  · apply integral_congr_ae
    filter_upwards [testVector_ae φ e] with x hx
    simp [hx, real_inner_smul_left, mul_comm]

omit [BorelSpace E] in
/-- Membership in the plane graph is exactly the raw ordered weak identities. -/
theorem mem_planeHkGraph_iff (D : JetL2 (volume.restrict U) K E) :
    D ∈ planeHkGraph (E := E) U K ↔
      HasOrderedWeakJetOn U (planeJetRepresentative D) := by
  simp only [planeHkGraph, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot]
  constructor
  · intro h j w i e φ hφ hc hs
    have hcst := h j w i ⟨φ, hφ, hc, hs⟩ e
    rw [weakJetConstraint_apply] at hcst
    exact eq_neg_of_add_eq_zero_left hcst
  · intro h j w i φ e
    rw [weakJetConstraint_apply]
    have hw := h j w i e φ.toFun φ.smooth φ.compact φ.support_subset
    exact add_eq_zero_iff_eq_neg.mpr hw

/-- Promote every raw derivative to its `L²` class. -/
def jetToL2 (D : RawJet2 K E) (hD : JetMemL2On U D) :
    JetL2 (volume.restrict U) K E :=
  WithLp.toLp 2 (fun a => (hD a).toLp (D a))

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Promotion preserves every raw component almost everywhere. -/
theorem jetToL2_ae (D : RawJet2 K E) (hD : JetMemL2On U D) (a : JetIndex2 K) :
    planeJetRepresentative (jetToL2 D hD) a =ᵐ[volume.restrict U] D a :=
  (hD a).coeFn_toLp

/-- The weak identities are invariant under changing both representatives a.e. -/
theorem hasWeakPartialDerivOn_congr_ae {i : Fin 2} {u v g h : Vec 2 → ℝ}
    (huv : u =ᵐ[volume.restrict U] v) (hgh : g =ᵐ[volume.restrict U] h)
    (hw : HasWeakPartialDerivOn U i u g) : HasWeakPartialDerivOn U i v h := by
  intro φ hφ hc hs
  calc
    (∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂volume) =
        ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
      apply integral_congr_ae
      filter_upwards [huv] with x hx
      rw [hx]
    _ = -(∫ x in U, g x * φ x ∂volume) := hw φ hφ hc hs
    _ = -(∫ x in U, h x * φ x ∂volume) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hgh] with x hx
      rw [hx]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Ordered weak identities are invariant under componentwise a.e. equality. -/
theorem hasOrderedWeakJetOn_congr_ae {D F : RawJet2 K E}
    (hDF : ∀ a, D a =ᵐ[volume.restrict U] F a) (hD : HasOrderedWeakJetOn U D) :
    HasOrderedWeakJetOn U F := by
  intro j w i e
  apply hasWeakPartialDerivOn_congr_ae _ _ (hD j w i e)
  · filter_upwards [hDF (lowerIndex2 j w)] with x hx
    rw [hx]
  · filter_upwards [hDF (nextIndex2 j w i)] with x hx
    rw [hx]

/-- A raw plane witness determines an element of the closed Hilbert graph. -/
def PlaneHkFunction.toHk (f : PlaneHkFunction U K E) : PlaneHk U K E :=
  ⟨jetToL2 f.jet f.memL2,
    (mem_planeHkGraph_iff (jetToL2 f.jet f.memL2)).2
      (hasOrderedWeakJetOn_congr_ae
        (fun a => (jetToL2_ae f.jet f.memL2 a).symm) f.hasWeakJet)⟩

/-- Every plane graph element has raw representatives and their weak identities. -/
def PlaneHk.toFunction (f : PlaneHk U K E) : PlaneHkFunction U K E where
  jet := planeJetRepresentative f.val
  memL2 := fun a => Lp.memLp (f.val a)
  hasWeakJet := (mem_planeHkGraph_iff f.val).mp f.property

/-- Promoting a graph representative returns the original Hilbert element. -/
theorem PlaneHk.toFunction_toHk (f : PlaneHk U K E) : f.toFunction.toHk = f := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  exact Lp.toLp_coeFn (f.val a) (Lp.memLp (f.val a))

/-- Promoting a raw plane witness returns its components almost everywhere. -/
theorem PlaneHkFunction.toHk_toFunction_ae (f : PlaneHkFunction U K E) :
    ∀ a, f.toHk.toFunction.jet a =ᵐ[volume.restrict U] f.jet a := by
  intro a
  exact jetToL2_ae f.jet f.memL2 a

omit [MeasurableSpace E] [BorelSpace E] in
/-- Vector-valued weak derivatives are unique on open domains. -/
theorem weakDerivative_unique [FiniteDimensional ℝ E] (hU : IsOpen U) {i : Fin 2}
    {u g h : Vec 2 → E} (hg : MemLp g 2 (volume.restrict U))
    (hh : MemLp h 2 (volume.restrict U))
    (hgw : ∀ e : E, HasWeakPartialDerivOn U i (fun x => inner ℝ e (u x))
      (fun x => inner ℝ e (g x)))
    (hhw : ∀ e : E, HasWeakPartialDerivOn U i (fun x => inner ℝ e (u x))
      (fun x => inner ℝ e (h x))) : g =ᵐ[volume.restrict U] h := by
  let b := stdOrthonormalBasis ℝ E
  have hp : ∀ a, (fun x => inner ℝ (b a) (g x)) =ᵐ[volume.restrict U]
      (fun x => inner ℝ (b a) (h x)) := by
    intro a
    have hg' : MemLp (fun x => inner ℝ (b a) (g x)) 2 (volume.restrict U) :=
      (InnerProductSpace.toDual ℝ E (b a)).comp_memLp' hg
    have hh' : MemLp (fun x => inner ℝ (b a) (h x)) 2 (volume.restrict U) :=
      (InnerProductSpace.toDual ℝ E (b a)).comp_memLp' hh
    exact HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        (hg'.locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        (hh'.locallyIntegrable (by norm_num))) (hgw (b a)) (hhw (b a))
  have hpall : ∀ᵐ x ∂volume.restrict U, ∀ a,
      inner ℝ (b a) (g x) = inner ℝ (b a) (h x) := ae_all_iff.mpr hp
  filter_upwards [hpall] with x hx
  apply b.repr.injective
  ext a
  simpa only [b.repr_apply_apply] using hx a

omit [MeasurableSpace E] [BorelSpace E] in
/-- The order-zero component uniquely determines a plane weak jet. -/
theorem orderedWeakJet_unique [FiniteDimensional ℝ E] (hU : IsOpen U)
    {D F : RawJet2 K E} (hD : JetMemL2On U D) (hF : JetMemL2On U F)
    (hDw : HasOrderedWeakJetOn U D) (hFw : HasOrderedWeakJetOn U F)
    (h0 : D (valueIndex2 K) =ᵐ[volume.restrict U] F (valueIndex2 K)) :
    ∀ a, D a =ᵐ[volume.restrict U] F a := by
  have hlevels : ∀ j, ∀ (hj : j < K + 1), ∀ w : DerivativeWord2 j,
      D ⟨⟨j, hj⟩, w⟩ =ᵐ[volume.restrict U] F ⟨⟨j, hj⟩, w⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj w
      have hw : w = Fin.elim0 := by funext a; exact Fin.elim0 a
      simpa [valueIndex2, valueIndex, hw] using h0
    | succ j ih =>
      intro hj w
      let k : Fin K := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      let v : DerivativeWord2 j := Fin.init w
      let i : Fin 2 := w (Fin.last j)
      have hn : nextIndex2 k v i = ⟨⟨j + 1, hj⟩, w⟩ := by
        simp [nextIndex2, nextIndex, k, v, i]
      have hp : D (lowerIndex2 k v) =ᵐ[volume.restrict U] F (lowerIndex2 k v) :=
        ih (Nat.lt_of_succ_lt hj) v
      rw [← hn]
      apply weakDerivative_unique hU (hD (nextIndex2 k v i)) (hF (nextIndex2 k v i))
        (hDw k v i)
      intro e
      apply hasWeakPartialDerivOn_congr_ae _ (Filter.Eventually.of_forall (fun _ => rfl))
        (hFw k v i e)
      filter_upwards [hp] with x hx
      rw [hx]
  intro a
  exact hlevels a.1.val a.1.isLt a.2

/-- Equality of order-zero `L²` components implies equality in `PlaneHk`. -/
theorem PlaneHk.ext_value [FiniteDimensional ℝ E] (hU : IsOpen U)
    {f g : PlaneHk U K E} (h0 : f.val (valueIndex2 K) = g.val (valueIndex2 K)) : f = g := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  apply orderedWeakJet_unique hU f.toFunction.memL2 g.toFunction.memL2
    f.toFunction.hasWeakJet g.toFunction.hasWeakJet _ a
  exact Filter.EventuallyEq.of_eq
    (congrArg (fun z : ComponentL2 (volume.restrict U) E => (z : Vec 2 → E)) h0)
end

/-! Raw and Hilbert realizations of periodic weak Sobolev jets. -/

section
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {K : ℕ}

omit [BorelSpace E] [CompleteSpace E] in
/-- A cell pairing with vector-valued test data reads the periodic extension. -/
theorem cellTestPairing_eq (D : JetL2 (volume.restrict AVenhance.unitCube) K E)
    (a : JetIndex2 K) (ψ : Vec 2 → ℝ)
    (hψ : MemLp ψ 2 (volume.restrict AVenhance.unitCube)) (e : E) :
    inner ℝ (cellTestVectorL2 ψ hψ e) (D a) =
      ∫ x in AVenhance.unitCube,
        inner ℝ e (periodicJetRepresentative D a x) * ψ x ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cellTestVectorL2_ae ψ hψ e, periodicJetRepresentative_ae D a] with x htest hx
  simp [htest, hx, real_inner_smul_left, mul_comm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Global pairings of periodic raw data reduce to cell pairings. -/
theorem periodicRawPairing_eq_cell (F : RawJet2 K E)
    (hperiodic : ∀ a, AVenhance.IsZ2Periodic (F a))
    (hmem : JetMemL2On AVenhance.unitCube F) (a : JetIndex2 K) (e : E)
    {ψ : Vec 2 → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    (∫ x, inner ℝ e (F a x) * ψ x ∂volume) =
      ∫ x in AVenhance.unitCube,
        inner ℝ e (F a x) * compactTestPeriodization ψ x ∂volume := by
  have hg : MemLp (fun x => inner ℝ e (F a x)) 2
      (volume.restrict AVenhance.unitCube) :=
    (InnerProductSpace.toDual ℝ E e).comp_memLp' (hmem a)
  have hp : AVenhance.IsZ2Periodic (fun x => inner ℝ e (F a x)) := by
    intro n x
    exact congrArg (inner ℝ e) (hperiodic a n x)
  have h := (WeakGradientPeriodization.integral_periodic_mul_compact_eq_cell_periodization
    hg hp hψ hc).2
  rw [setIntegral_congr_set WeakGradientPeriodization.periodCell_ae_unitCube] at h
  exact h

omit [BorelSpace E] in
/-- A global compact-test pairing of a Hilbert jet unfolds to the cell. -/
theorem periodicWeakJetConstraint_apply
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (j : Fin K)
    (w : DerivativeWord2 j.val) (i : Fin 2)
    (φ : WeakTest (Set.univ : Set (Vec 2))) (e : E) :
    periodicWeakJetConstraint j w i φ e D =
      (∫ x, inner ℝ e (periodicJetRepresentative D (lowerIndex2 j w) x) *
        φ.coordDeriv i x ∂volume) +
      (∫ x, inner ℝ e (periodicJetRepresentative D (nextIndex2 j w i) x) *
        φ.toFun x ∂volume) := by
  change inner ℝ (periodizedPartialTestVectorL2 φ i e) (D (lowerIndex2 j w)) +
      inner ℝ (periodizedTestVectorL2 φ e) (D (nextIndex2 j w i)) = _
  rw [periodizedPartialTestVectorL2, periodizedTestVectorL2,
    cellTestPairing_eq, cellTestPairing_eq]
  congr 1
  · symm
    exact periodicRawPairing_eq_cell (periodicJetRepresentative D)
      (periodicJetRepresentative_periodic D) (periodicJetRepresentative_memL2 D)
      (lowerIndex2 j w) e
      ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      (φ.compact.fderiv_apply (𝕜 := ℝ) (basisVec i))
  · exact (periodicRawPairing_eq_cell (periodicJetRepresentative D)
      (periodicJetRepresentative_periodic D) (periodicJetRepresentative_memL2 D)
      (nextIndex2 j w i) e φ.smooth.continuous φ.compact).symm

omit [BorelSpace E] in
/-- The raw periodic predicate is exactly membership in the closed torus graph. -/
theorem mem_torusHkGraph_iff (D : JetL2 (volume.restrict AVenhance.unitCube) K E) :
    D ∈ torusHkGraph (E := E) K ↔
      HasPeriodicOrderedWeakJet (periodicJetRepresentative D) := by
  simp only [torusHkGraph, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot]
  constructor
  · intro h
    refine ⟨periodicJetRepresentative_periodic D,
      periodicJetRepresentative_memL2 D, ?_⟩
    intro j w i e φ hφ hc hs
    have ht := h j w i ⟨φ, hφ, hc, hs⟩ e
    rw [periodicWeakJetConstraint_apply] at ht
    simpa only [setIntegral_univ, WeakTest.coordDeriv] using eq_neg_of_add_eq_zero_left ht
  · rintro ⟨hper, hmem, hweak⟩ j w i φ e
    rw [periodicWeakJetConstraint_apply]
    have hw := hweak j w i e φ.toFun φ.smooth φ.compact φ.support_subset
    simpa only [setIntegral_univ, WeakTest.coordDeriv] using add_eq_zero_iff_eq_neg.mpr hw

/-- Promote all components of a raw periodic jet to their cell `L²` classes. -/
def torusJetToL2 (D : RawJet2 K E) (hD : JetMemL2On AVenhance.unitCube D) :
    JetL2 (volume.restrict AVenhance.unitCube) K E :=
  WithLp.toLp 2 (fun a => (hD a).toLp (D a))

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Promotion preserves each cell component almost everywhere. -/
theorem torusJetToL2_ae (D : RawJet2 K E) (hD : JetMemL2On AVenhance.unitCube D)
    (a : JetIndex2 K) :
    torusJetToL2 D hD a =ᵐ[volume.restrict AVenhance.unitCube] D a :=
  (hD a).coeFn_toLp

omit [BorelSpace E] [CompleteSpace E] in
/-- A cell pairing of promoted raw data reads the original raw component. -/
theorem cellTestPairing_raw_eq (F : RawJet2 K E)
    (hF : JetMemL2On AVenhance.unitCube F) (a : JetIndex2 K)
    (ψ : Vec 2 → ℝ) (hψ : MemLp ψ 2 (volume.restrict AVenhance.unitCube)) (e : E) :
    inner ℝ (cellTestVectorL2 ψ hψ e) (torusJetToL2 F hF a) =
      ∫ x in AVenhance.unitCube, inner ℝ e (F a x) * ψ x ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cellTestVectorL2_ae ψ hψ e, torusJetToL2_ae F hF a] with x ht hx
  simp only [ht, hx]
  rw [real_inner_smul_left]
  ring

omit [BorelSpace E] in
/-- A raw periodic witness gives a point of the torus Hilbert graph. -/
theorem torusJetToL2_mem_graph (f : TorusHkFunction K E) :
    torusJetToL2 f.jet f.hasPeriodicWeakJet.2.1 ∈ torusHkGraph (E := E) K := by
  simp only [torusHkGraph, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot]
  intro j w i φ e
  change inner ℝ (periodizedPartialTestVectorL2 φ i e)
      (torusJetToL2 f.jet f.hasPeriodicWeakJet.2.1 (lowerIndex2 j w)) +
    inner ℝ (periodizedTestVectorL2 φ e)
      (torusJetToL2 f.jet f.hasPeriodicWeakJet.2.1 (nextIndex2 j w i)) = 0
  rw [periodizedPartialTestVectorL2, periodizedTestVectorL2,
    cellTestPairing_raw_eq, cellTestPairing_raw_eq]
  rw [← periodicRawPairing_eq_cell (ψ := φ.coordDeriv i) f.jet
      f.hasPeriodicWeakJet.1 f.hasPeriodicWeakJet.2.1 (lowerIndex2 j w) e
      ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      (φ.compact.fderiv_apply (𝕜 := ℝ) (basisVec i)),
    ← periodicRawPairing_eq_cell f.jet f.hasPeriodicWeakJet.1 f.hasPeriodicWeakJet.2.1
      (nextIndex2 j w i) e φ.smooth.continuous φ.compact]
  have hw := f.hasPeriodicWeakJet.2.2 j w i e φ.toFun φ.smooth φ.compact φ.support_subset
  simpa only [setIntegral_univ, WeakTest.coordDeriv] using add_eq_zero_iff_eq_neg.mpr hw

/-- Canonical promotion of a raw periodic witness to `TorusHk`. -/
def TorusHkFunction.toHk (f : TorusHkFunction K E) : TorusHk K E :=
  ⟨torusJetToL2 f.jet f.hasPeriodicWeakJet.2.1, torusJetToL2_mem_graph f⟩

/-- Every torus graph element has periodic raw representatives. -/
def TorusHk.toFunction (f : TorusHk K E) : TorusHkFunction K E where
  jet := periodicJetRepresentative f.val
  hasPeriodicWeakJet := (mem_torusHkGraph_iff f.val).mp f.property

/-- Promoting canonical torus representatives returns the original element. -/
theorem TorusHk.toFunction_toHk (f : TorusHk K E) : f.toFunction.toHk = f := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  exact (torusJetToL2_ae f.toFunction.jet f.toFunction.hasPeriodicWeakJet.2.1 a).trans
    (periodicJetRepresentative_ae f.val a)

/-- Promoting a raw periodic witness returns its components almost everywhere on the cell. -/
theorem TorusHkFunction.toHk_toFunction_ae (f : TorusHkFunction K E) :
    ∀ a, f.toHk.toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube] f.jet a := by
  intro a
  exact (periodicJetRepresentative_ae (torusJetToL2 f.jet f.hasPeriodicWeakJet.2.1) a).trans
    (torusJetToL2_ae f.jet f.hasPeriodicWeakJet.2.1 a)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- A periodic weak jet restricts to ordinary weak identities on the unit cell. -/
theorem HasPeriodicOrderedWeakJet.hasWeakJetOn_cell {F : RawJet2 K E}
    (hF : HasPeriodicOrderedWeakJet F) : HasOrderedWeakJetOn AVenhance.unitCube F := by
  intro j w i e
  apply (hF.2.2 j w i e).restrict _ (Set.subset_univ _)
  simpa [AVenhance.unitCube] using
    (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo))

/-- The value class uniquely determines all periodic derivative classes. -/
theorem TorusHk.ext_value [FiniteDimensional ℝ E]
    {f g : TorusHk K E} (h0 : f.val (valueIndex2 K) = g.val (valueIndex2 K)) : f = g := by
  have ho : IsOpen AVenhance.unitCube := by
    simpa [AVenhance.unitCube] using
      (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo))
  have hbase : f.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      g.toFunction.jet (valueIndex2 K) :=
    (periodicJetRepresentative_ae f.val (valueIndex2 K)).trans
      ((Filter.EventuallyEq.of_eq (congrArg
        (fun z : ComponentL2 (volume.restrict AVenhance.unitCube) E =>
          (z : Vec 2 → E)) h0)).trans
        (periodicJetRepresentative_ae g.val (valueIndex2 K)).symm)
  have hall := orderedWeakJet_unique ho f.toFunction.hasPeriodicWeakJet.2.1
    g.toFunction.hasPeriodicWeakJet.2.1
    f.toFunction.hasPeriodicWeakJet.hasWeakJetOn_cell
    g.toFunction.hasPeriodicWeakJet.hasWeakJetOn_cell hbase
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  exact (periodicJetRepresentative_ae f.val a).symm.trans
    ((hall a).trans (periodicJetRepresentative_ae g.val a))
end

end AVRegularity.Sobolev
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Sobolev

/-! Contractive truncations and ordered derivative maps. -/

section FiniteProjection
variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull back a finite Hilbert family along an index map. -/
def familyPullback (g : ι → κ) :
    PiLp 2 (fun _ : κ => E) →L[ℝ] PiLp 2 (fun _ : ι => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => PiLp.proj (𝕜 := ℝ) 2 (fun _ : κ => E) (g i)))

omit [Fintype ι] [Fintype κ] in
@[simp] theorem familyPullback_apply (g : ι → κ) (D : PiLp 2 (fun _ : κ => E)) (i : ι) :
    familyPullback g D i = D (g i) := rfl

/-- Injective selection of a finite Hilbert family is a contraction. -/
theorem familyPullback_norm_le (g : ι → κ) (hg : Function.Injective g)
    (D : PiLp 2 (fun _ : κ => E)) : ‖familyPullback g D‖ ≤ ‖D‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [familyPullback_apply]
  calc
    (∑ i : ι, ‖D (g i)‖ ^ 2) = ∑ k ∈ Finset.univ.image g, ‖D k‖ ^ 2 := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact hg hab
    _ ≤ ∑ k : κ, ‖D k‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => sq_nonneg ‖D k‖)

end FiniteProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {μ : Measure (Vec 2)} {K L r : ℕ}

/-- Include an index of order `K` in a jet of order `L`, when `K ≤ L`. -/
def truncateJetIndex (hKL : K ≤ L) (a : JetIndex2 K) : JetIndex2 L :=
  ⟨⟨a.1.val, Nat.lt_of_lt_of_le a.1.isLt (Nat.succ_le_succ hKL)⟩, a.2⟩

/-- Lower-order index inclusion is injective. -/
theorem truncateJetIndex_injective (hKL : K ≤ L) :
    Function.Injective (truncateJetIndex (K := K) (L := L) hKL) := by
  rintro ⟨j, w⟩ ⟨k, v⟩ h
  have hj : j = k := Fin.ext (congrArg (fun a : JetIndex2 L => a.1.val) h)
  cases hj
  have hw : w = v := by simpa [truncateJetIndex] using h
  cases hw
  rfl

/-- The ambient lower-order projection of ordered jets. -/
def truncateJet (hKL : K ≤ L) : JetL2 μ L E →L[ℝ] JetL2 μ K E :=
  familyPullback (truncateJetIndex hKL)

omit [BorelSpace E] [CompleteSpace E] in
@[simp] theorem truncateJet_apply (hKL : K ≤ L) (D : JetL2 μ L E) (a : JetIndex2 K) :
    truncateJet hKL D a = D (truncateJetIndex hKL a) := rfl

omit [BorelSpace E] [CompleteSpace E] in
/-- Ambient lower-order projection is a contraction in the unweighted norm. -/
theorem truncateJet_norm_le (hKL : K ≤ L) (D : JetL2 μ L E) :
    ‖truncateJet hKL D‖ ≤ ‖D‖ :=
  familyPullback_norm_le _ (truncateJetIndex_injective hKL) D

omit [BorelSpace E] in
/-- Truncation preserves the plane weak derivative graph. -/
theorem truncateJet_mem_planeGraph {U : Set (Vec 2)} (hKL : K ≤ L)
    {D : JetL2 (volume.restrict U) L E} (hD : D ∈ planeHkGraph (E := E) U L) :
    truncateJet hKL D ∈ planeHkGraph (E := E) U K := by
  rw [mem_planeHkGraph_iff] at hD ⊢
  intro j w i e
  let j' : Fin L := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hKL⟩
  have hl : truncateJetIndex hKL (lowerIndex2 j w) = lowerIndex2 j' w := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  have hn : truncateJetIndex hKL (nextIndex2 j w i) = nextIndex2 j' w i := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  have hh := hD j' w i e
  simpa [planeJetRepresentative, truncateJet_apply, hl, hn] using hh

omit [BorelSpace E] in
/-- Truncation preserves the periodic weak derivative graph. -/
theorem truncateJet_mem_torusGraph (hKL : K ≤ L)
    {D : JetL2 (volume.restrict AVenhance.unitCube) L E}
    (hD : D ∈ torusHkGraph (E := E) L) :
    truncateJet hKL D ∈ torusHkGraph (E := E) K := by
  rw [mem_torusHkGraph_iff] at hD ⊢
  rcases hD with ⟨hper, hmem, hweak⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a n x
    simpa [periodicJetRepresentative, truncateJet, familyPullback,
      truncateJetIndex] using hper (truncateJetIndex hKL a) n x
  · intro a
    simpa [periodicJetRepresentative, truncateJet, familyPullback,
      truncateJetIndex] using hmem (truncateJetIndex hKL a)
  · intro j w i e
    let j' : Fin L := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hKL⟩
    have hl : truncateJetIndex hKL (lowerIndex2 j w) = lowerIndex2 j' w := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · rfl
    have hn : truncateJetIndex hKL (nextIndex2 j w i) = nextIndex2 j' w i := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · rfl
    have hh := hweak j' w i e
    simpa [periodicJetRepresentative, truncateJet, familyPullback, hl, hn] using hh

/-- Bounded truncation on the plane Sobolev carrier. -/
def truncatePlaneHk {U : Set (Vec 2)} (hKL : K ≤ L) :
    PlaneHk U L E →L[ℝ] PlaneHk U K E :=
  ((truncateJet hKL).comp (planeHkGraph (E := E) U L).toSubmodule.subtypeL).codRestrict
    (planeHkGraph (E := E) U K).toSubmodule
    (fun f => truncateJet_mem_planeGraph hKL f.property)

@[simp] theorem truncatePlaneHk_apply {U : Set (Vec 2)} (hKL : K ≤ L)
    (f : PlaneHk U L E) (a : JetIndex2 K) :
    (truncatePlaneHk hKL f).val a = f.val (truncateJetIndex hKL a) := rfl

/-- Plane Sobolev truncation is a contraction. -/
theorem truncatePlaneHk_norm_le {U : Set (Vec 2)} (hKL : K ≤ L)
    (f : PlaneHk U L E) : ‖truncatePlaneHk hKL f‖ ≤ ‖f‖ := by
  change ‖truncateJet hKL f.val‖ ≤ ‖f.val‖
  exact truncateJet_norm_le hKL f.val

/-- Bounded truncation on the torus Sobolev carrier. -/
def truncateTorusHk (hKL : K ≤ L) : TorusHk L E →L[ℝ] TorusHk K E :=
  ((truncateJet hKL).comp (torusHkGraph (E := E) L).toSubmodule.subtypeL).codRestrict
    (torusHkGraph (E := E) K).toSubmodule
    (fun f => truncateJet_mem_torusGraph hKL f.property)

@[simp] theorem truncateTorusHk_apply (hKL : K ≤ L) (f : TorusHk L E)
    (a : JetIndex2 K) : (truncateTorusHk hKL f).val a = f.val (truncateJetIndex hKL a) := rfl

/-- Torus Sobolev truncation is a contraction. -/
theorem truncateTorusHk_norm_le (hKL : K ≤ L) (f : TorusHk L E) :
    ‖truncateTorusHk hKL f‖ ≤ ‖f‖ := by
  change ‖truncateJet hKL f.val‖ ≤ ‖f.val‖
  exact truncateJet_norm_le hKL f.val

/-- Concatenating two ordered words identifies the product with their combined word. -/
def wordAppendEquiv (r j : ℕ) :
    (DerivativeWord2 r × DerivativeWord2 j) ≃ DerivativeWord2 (r + j) where
  toFun a := Fin.append a.1 a.2
  invFun w := ⟨fun i => w (Fin.castAdd j i), fun i => w (Fin.natAdd r i)⟩
  left_inv a := by
    apply Prod.ext <;> funext i <;> simp
  right_inv w := Fin.append_castAdd_natAdd

/-- Append a fixed derivative prefix to an index of a lower-order jet. -/
def prefixJetIndex (a : DerivativeWord2 r) (b : JetIndex2 K) : JetIndex2 (K + r) :=
  ⟨⟨r + b.1.val, by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_lt_add_left b.1.isLt r⟩, Fin.append a b.2⟩

/-- A fixed prefix selects distinct entries of the higher jet. -/
theorem prefixJetIndex_injective (a : DerivativeWord2 r) :
    Function.Injective (prefixJetIndex (K := K) (r := r) a) := by
  rintro ⟨j, w⟩ ⟨k, v⟩ h
  have hj : j = k := Fin.ext
    (Nat.add_left_cancel (congrArg (fun b : JetIndex2 (K + r) => b.1.val) h))
  cases hj
  have hw : Fin.append a w = Fin.append a v := by simpa [prefixJetIndex] using h
  have hv : w = v := by
    funext i
    simpa using congrFun hw (Fin.natAdd r i)
  cases hv
  rfl

/-- Extract an ordered derivative prefix as a bounded map of ambient jets. -/
def derivativeJet (a : DerivativeWord2 r) :
    JetL2 μ (K + r) E →L[ℝ] JetL2 μ K E := familyPullback (prefixJetIndex a)

omit [BorelSpace E] [CompleteSpace E] in
@[simp] theorem derivativeJet_apply (a : DerivativeWord2 r)
    (D : JetL2 μ (K + r) E) (b : JetIndex2 K) :
    derivativeJet a D b = D (prefixJetIndex a b) := rfl

omit [BorelSpace E] [CompleteSpace E] in
/-- Extracting one derivative prefix is a contraction in the unweighted norm. -/
theorem derivativeJet_norm_le (a : DerivativeWord2 r) (D : JetL2 μ (K + r) E) :
    ‖derivativeJet a D‖ ≤ ‖D‖ :=
  familyPullback_norm_le _ (prefixJetIndex_injective a) D

omit [BorelSpace E] in
/-- Derivative extraction preserves the plane weak graph. -/
theorem derivativeJet_mem_planeGraph {U : Set (Vec 2)} (a : DerivativeWord2 r)
    {D : JetL2 (volume.restrict U) (K + r) E}
    (hD : D ∈ planeHkGraph (E := E) U (K + r)) :
    derivativeJet a D ∈ planeHkGraph (E := E) U K := by
  rw [mem_planeHkGraph_iff] at hD ⊢
  intro j w i e
  let j' : Fin (K + r) := ⟨r + j.val, by
    simpa [Nat.add_comm] using Nat.add_lt_add_left j.isLt r⟩
  have hh := hD j' (Fin.append a w) i e
  simpa only [planeJetRepresentative, derivativeJet_apply, prefixJetIndex,
    lowerIndex2, lowerIndex, nextIndex2, nextIndex, Fin.append_snoc, j', Nat.add_succ] using hh

omit [BorelSpace E] in
/-- Derivative extraction preserves the periodic weak graph. -/
theorem derivativeJet_mem_torusGraph (a : DerivativeWord2 r)
    {D : JetL2 (volume.restrict AVenhance.unitCube) (K + r) E}
    (hD : D ∈ torusHkGraph (E := E) (K + r)) :
    derivativeJet a D ∈ torusHkGraph (E := E) K := by
  rw [mem_torusHkGraph_iff] at hD ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro b n x
    simpa [periodicJetRepresentative, derivativeJet_apply, prefixJetIndex] using
      hD.1 (prefixJetIndex a b) n x
  · intro b
    simpa [periodicJetRepresentative, derivativeJet_apply, prefixJetIndex] using
      hD.2.1 (prefixJetIndex a b)
  · intro j w i e
    let j' : Fin (K + r) := ⟨r + j.val, by
      simpa [Nat.add_comm] using Nat.add_lt_add_left j.isLt r⟩
    have hh := hD.2.2 j' (Fin.append a w) i e
    simpa only [periodicJetRepresentative, derivativeJet_apply, prefixJetIndex,
      lowerIndex2, lowerIndex, nextIndex2, nextIndex, Fin.append_snoc, j', Nat.add_succ] using hh

/-- Ordered derivative map from `PlaneHk(K+r)` to `PlaneHk(K)`. -/
def derivativePlaneHk {U : Set (Vec 2)} (a : DerivativeWord2 r) :
    PlaneHk U (K + r) E →L[ℝ] PlaneHk U K E :=
  ((derivativeJet a).comp (planeHkGraph (E := E) U (K + r)).toSubmodule.subtypeL).codRestrict
    (planeHkGraph (E := E) U K).toSubmodule (fun f => derivativeJet_mem_planeGraph a f.property)

@[simp] theorem derivativePlaneHk_apply {U : Set (Vec 2)} (a : DerivativeWord2 r)
    (f : PlaneHk U (K + r) E) (b : JetIndex2 K) :
    (derivativePlaneHk a f).val b = f.val (prefixJetIndex a b) := rfl

/-- An ordered weak derivative map has unweighted norm at most one. -/
theorem derivativePlaneHk_norm_le {U : Set (Vec 2)} (a : DerivativeWord2 r)
    (f : PlaneHk U (K + r) E) : ‖derivativePlaneHk a f‖ ≤ ‖f‖ := by
  change ‖derivativeJet a f.val‖ ≤ ‖f.val‖
  exact derivativeJet_norm_le a f.val

/-- Ordered derivative map from `TorusHk(K+r)` to `TorusHk(K)`. -/
def derivativeTorusHk (a : DerivativeWord2 r) :
    TorusHk (K + r) E →L[ℝ] TorusHk K E :=
  ((derivativeJet a).comp (torusHkGraph (E := E) (K + r)).toSubmodule.subtypeL).codRestrict
    (torusHkGraph (E := E) K).toSubmodule (fun f => derivativeJet_mem_torusGraph a f.property)

@[simp] theorem derivativeTorusHk_apply (a : DerivativeWord2 r)
    (f : TorusHk (K + r) E) (b : JetIndex2 K) :
    (derivativeTorusHk a f).val b = f.val (prefixJetIndex a b) := rfl

/-- A periodic ordered weak derivative map has unweighted norm at most one. -/
theorem derivativeTorusHk_norm_le (a : DerivativeWord2 r)
    (f : TorusHk (K + r) E) : ‖derivativeTorusHk a f‖ ≤ ‖f‖ := by
  change ‖derivativeJet a f.val‖ ≤ ‖f.val‖
  exact derivativeJet_norm_le a f.val

end AVRegularity.Sobolev
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization
namespace AVRegularity.Sobolev

/-! The Sobolev shift cost is inherited from the shared factorial sequence lemma. -/

/-- The exact cost of reserving `r` derivative levels at radius `ρ`. -/
def derivativeReserveFactor (ρ : ℝ) (K r : ℕ) : ℝ :=
  (ρ ^ r)⁻¹ * ((K + r).factorial : ℝ) / (K.factorial : ℝ)

/-- The squared order-`j` weight is controlled by the shared sequence shift bound. -/
theorem factorialWeight_reserve_le (ρ : ℝ) (hρ : 0 < ρ) {j K : ℕ}
    (hj : j ≤ K) (r : ℕ) :
    ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2 ≤
      (derivativeReserveFactor ρ K r) ^ 2 *
        (ρ ^ (2 * (j + r)) / ((j + r).factorial : ℝ) ^ 2) := by
  let w : ℕ → NNReal := fun n => if n = j + r then 1 else 0
  let W := AVRegularity.Analysis.Factorial.factorialWeight ρ
  have hjmem : j ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hjrmem : j + r ∈ Finset.range (K + r + 1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.add_le_add_right hj r)
  have hleftsum :
      (∑ n ∈ Finset.range (K + 1), (W n * (w (n + r) : ℝ)) ^ 2) = (W j) ^ 2 := by
    rw [Finset.sum_eq_single_of_mem j hjmem]
    · simp [w]
    · intro n hn hnj
      have hz : w (n + r) = 0 := by
        simp only [w]
        split_ifs with h
        · exact False.elim (hnj (Nat.add_right_cancel h))
        · rfl
      simp [hz]
  have hrightsum :
      (∑ n ∈ Finset.range (K + r + 1), (W n * (w n : ℝ)) ^ 2) = (W (j + r)) ^ 2 := by
    rw [Finset.sum_eq_single_of_mem (j + r) hjrmem]
    · simp [w]
    · intro n hn hnj
      have hz : w n = 0 := by
        simp only [w]
        split_ifs with h
        · exact False.elim (hnj h)
        · rfl
      simp [hz]
  have hleft :
      Real.sqrt (∑ n ∈ Finset.range (K + 1), (W n * (w (n + r) : ℝ)) ^ 2) = W j := by
    have hWj : 0 ≤ W j := by
      dsimp [W, AVRegularity.Analysis.Factorial.factorialWeight]
      positivity
    rw [hleftsum, Real.sqrt_sq_eq_abs, abs_of_nonneg hWj]
  have hright :
      Real.sqrt (∑ n ∈ Finset.range (K + r + 1), (W n * (w n : ℝ)) ^ 2) = W (j + r) := by
    have hWjr : 0 ≤ W (j + r) := by
      dsimp [W, AVRegularity.Analysis.Factorial.factorialWeight]
      positivity
    rw [hrightsum, Real.sqrt_sq_eq_abs, abs_of_nonneg hWjr]
  have hshift := AVRegularity.Analysis.Factorial.factorialShiftInequality
    (K := K) (r := r) hρ w
  rw [hleft, hright] at hshift
  dsimp [W, derivativeReserveFactor] at hshift
  have hweight : ∀ n, 0 < AVRegularity.Analysis.Factorial.factorialWeight ρ n := by
    intro n
    unfold AVRegularity.Analysis.Factorial.factorialWeight
    exact div_pos (pow_pos hρ _) (by exact_mod_cast Nat.factorial_pos n)
  have hcost : 0 ≤ (ρ ^ r)⁻¹ * ((K + r).factorial : ℝ) / (K.factorial : ℝ) := by
    positivity
  have hroot0 :
      (AVRegularity.Analysis.Factorial.factorialWeight ρ j) ^ 2 ≤
        (((ρ ^ r)⁻¹ * ((K + r).factorial : ℝ) / (K.factorial : ℝ)) *
          AVRegularity.Analysis.Factorial.factorialWeight ρ (j + r)) ^ 2 :=
    (sq_le_sq₀ (hweight j).le
      (mul_nonneg hcost (hweight (j + r)).le)).mpr hshift
  have hroot : (AVRegularity.Analysis.Factorial.factorialWeight ρ j) ^ 2 ≤
      ((ρ ^ r)⁻¹ * ((K + r).factorial : ℝ) / (K.factorial : ℝ)) ^ 2 *
        (AVRegularity.Analysis.Factorial.factorialWeight ρ (j + r)) ^ 2 := by
    simpa only [mul_pow] using hroot0
  have hweightSq (n : ℕ) :
      (AVRegularity.Analysis.Factorial.factorialWeight ρ n) ^ 2 =
        ρ ^ (2 * n) / (n.factorial : ℝ) ^ 2 := by
    unfold AVRegularity.Analysis.Factorial.factorialWeight
    rw [div_pow, ← pow_mul, Nat.mul_comm]
  rw [← hweightSq j, ← hweightSq (j + r)]
  exact hroot

/-! Ordered derivative arrays obey the factorial shift estimate. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {μ : Measure (Vec 2)} {K r : ℕ}

/-- The order of a higher jet reached by shifting a lower order by `r`. -/
def shiftedJetOrder (j : Fin (K + 1)) : Fin (K + r + 1) :=
  ⟨r + j.val, by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_lt_add_left j.isLt r⟩

/-- Different retained derivative orders select different higher orders. -/
theorem shiftedJetOrder_injective : Function.Injective (shiftedJetOrder (K := K) (r := r)) := by
  intro j k h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

omit [BorelSpace E] [CompleteSpace E] in
/-- The full extracted order-`j` tensor has the source order-`r+j` squared norm. -/
theorem derivativeArray_normSq (D : JetL2 μ (K + r) E) (j : Fin (K + 1)) :
    (∑ a : DerivativeWord2 r, derivativeNormSq (derivativeJet a D) j) =
      derivativeNormSq D (shiftedJetOrder j) := by
  classical
  unfold derivativeNormSq
  change (∑ a : DerivativeWord2 r, ∑ w : DerivativeWord2 j.val,
    ‖D (prefixJetIndex a ⟨j, w⟩)‖ ^ 2) = _
  rw [← Fintype.sum_prod_type (fun a : DerivativeWord2 r × DerivativeWord2 j.val =>
    ‖D (prefixJetIndex a.1 ⟨j, a.2⟩)‖ ^ 2)]
  exact Fintype.sum_equiv (wordAppendEquiv r j.val) _ _ (fun a => rfl)

omit [BorelSpace E] [CompleteSpace E] in
/-- Reindex the factorial square of all order-`r` derivatives without dropping words. -/
theorem derivativeArray_factorialNormSq (ρ : ℝ) (D : JetL2 μ (K + r) E) :
    (∑ a : DerivativeWord2 r, factorialNormSq ρ (derivativeJet a D)) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        derivativeNormSq D (shiftedJetOrder j) := by
  unfold factorialNormSq
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, derivativeArray_normSq]

omit [BorelSpace E] [CompleteSpace E] in
/-- Every finite subset of nonnegative terms is bounded by their full sum. -/
theorem sum_comp_le_sum_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → κ) (hg : Function.Injective g) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) :
    (∑ i : ι, w (g i)) ≤ ∑ k : κ, w k := by
  classical
  calc
    (∑ i : ι, w (g i)) = ∑ k ∈ Finset.univ.image g, w k := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact hg hab
    _ ≤ ∑ k : κ, w k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hw k)

omit [BorelSpace E] [CompleteSpace E] in
/-- The exact squared factorial shift estimate on the ambient ordered derivative arrays. -/
theorem derivativeArray_factorialNormSq_le (ρ : ℝ) (hρ : 0 < ρ)
    (D : JetL2 μ (K + r) E) :
    (∑ a : DerivativeWord2 r, factorialNormSq ρ (derivativeJet a D)) ≤
      (derivativeReserveFactor ρ K r) ^ 2 * factorialNormSq ρ D := by
  rw [derivativeArray_factorialNormSq]
  calc
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        derivativeNormSq D (shiftedJetOrder j)) ≤
      ∑ j : Fin (K + 1), (derivativeReserveFactor ρ K r) ^ 2 *
        (factorialWeight ρ (r + j.val) * derivativeNormSq D (shiftedJetOrder j)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (derivativeNormSq_nonneg D _)
      simpa [factorialWeight, Nat.add_comm] using
        (factorialWeight_reserve_le ρ hρ (Nat.le_of_lt_succ j.isLt) r)
    _ = (derivativeReserveFactor ρ K r) ^ 2 *
        (∑ j : Fin (K + 1), factorialWeight ρ (r + j.val) *
          derivativeNormSq D (shiftedJetOrder j)) := by
      rw [Finset.mul_sum]
    _ ≤ (derivativeReserveFactor ρ K r) ^ 2 * factorialNormSq ρ D := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_comp_le_sum_nonneg shiftedJetOrder shiftedJetOrder_injective
        (fun j : Fin (K + r + 1) => factorialWeight ρ j.val * derivativeNormSq D j)
        (fun j => mul_nonneg (factorialWeight_nonneg ρ j.val) (derivativeNormSq_nonneg D j))

omit [BorelSpace E] [CompleteSpace E] in
/-- The square-root factorial shift estimate for ambient derivative arrays. -/
theorem derivativeArray_factorialNorm_le (ρ : ℝ) (hρ : 0 < ρ)
    (D : JetL2 μ (K + r) E) :
    Real.sqrt (∑ a : DerivativeWord2 r, factorialNormSq ρ (derivativeJet a D)) ≤
      derivativeReserveFactor ρ K r * Real.sqrt (factorialNormSq ρ D) := by
  calc
    Real.sqrt (∑ a : DerivativeWord2 r, factorialNormSq ρ (derivativeJet a D)) ≤
      Real.sqrt ((derivativeReserveFactor ρ K r) ^ 2 * factorialNormSq ρ D) :=
        Real.sqrt_le_sqrt (derivativeArray_factorialNormSq_le ρ hρ D)
    _ = derivativeReserveFactor ρ K r * Real.sqrt (factorialNormSq ρ D) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq]
      unfold derivativeReserveFactor
      positivity

/-- Factorial shift for genuine torus Sobolev derivatives, inherited from the jet algebra. -/
theorem derivativeTorusHk_factorialNorm_le (ρ : ℝ) (hρ : 0 < ρ)
    (f : TorusHk (K + r) E) :
    Real.sqrt (∑ a : DerivativeWord2 r,
      factorialNormSq ρ (derivativeTorusHk (K := K) a f).val) ≤
      derivativeReserveFactor ρ K r * Real.sqrt (factorialNormSq ρ f.val) :=
  derivativeArray_factorialNorm_le ρ hρ f.val
end

end AVRegularity.Sobolev
end
end
end
