import Transport.PhysicalProbe.Geometry
import OAI.NumberTheory.DirichletL.Detector.LowSlotScales

/-!
Transport of the slot-specific bounds in OpenAI Detector/LowSlotScales.lean,
commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; license: upstream-config/LICENSE.
-/

namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma transport_lowUnselectedProduct_norm_bound (totalWidth : ℝ) {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤totalWidth)
    (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(totalWidth:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤totalWidth :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(totalWidth:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem transport_eventually_original_slot_scales (x y totalWidth : ℝ)
    (hxy : x<y) (hgrow : totalWidth<2*x-y) {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤totalWidth) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^y/L ∧
      1≤(Z^y/L)^2/lowPhysicalScale C (Z^x/L) (Z^y/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^x/L) (Z^y/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^(x/2+(y-x)/12+(y/2)*δ:ℝ) := by
  filter_upwards [transport_eventually_compensated_source_scales x y totalWidth hxy hgrow C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (transport_lowUnselectedProduct_norm_bound totalWidth ell hell hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.ProbePhysical
end
end OAI
