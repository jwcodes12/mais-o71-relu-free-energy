import Coercivity

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace O71

def edge : ℝ → ℝ := (Ioo (0:ℝ) 1).indicator (fun u => u^(-(2/3):ℝ))
def cutoff (x : ℝ) := (Icc (-44:ℝ) 44).indicator (fun _ => (1:ℝ)) x
def angular (p : ℝ) := edge p + edge (1-p)
def weights (i : Fin 3) : ℝ → ℝ := if i = 0 then fun z => edge z + edge (-z) else cutoff
def width (w : ℝ × Triple) := 16 * (angular w.1 * ∏ i, weights i (w.2 i))

theorem width_integrable : Integrable width := by
  have h : Integrable edge := (integrable_indicator_iff measurableSet_Ioo).2
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num))
  have hc : Integrable cutoff := (integrable_indicator_iff measurableSet_Icc).2 (by simp)
  have hp : Integrable angular := h.add ((integrable_comp_sub_left edge 1).2 h)
  have hv (i : Fin 3) : Integrable (weights i) := by
    unfold weights
    split
    · exact h.add (by simpa only [zero_sub] using (integrable_comp_sub_left edge 0).2 h)
    · exact hc
  exact (hp.mul_prod (Integrable.fintype_prod hv)).const_mul 16

theorem width_measurable : Measurable width := by
  have h : Measurable edge := (by unfold edge; apply Measurable.indicator _ measurableSet_Ioo; fun_prop)
  have hc : Measurable cutoff := (by unfold cutoff; exact measurable_const.indicator measurableSet_Icc)
  have h' (i : Fin 3) : Measurable (weights i) := by unfold weights; split <;> fun_prop
  unfold width angular; fun_prop

/-- Width in the D coordinate may be infinite on the null plane of zero middle slope. -/
def tip : Set (ℝ × ℝ × Triple) := {w | 0 < w.1 ∧ (w.2.2 0 = 0 ∨ w.1 ≤ width w.2)}

theorem tip_measurable : MeasurableSet tip := by
  unfold tip; exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_singleton (0:ℝ) |>.preimage (by fun_prop)).union
      (measurableSet_le measurable_fst (width_measurable.comp measurable_snd)))

theorem tip_finite : volume tip ≠ ∞ := by
  rw [volume_eq_prod,prod_apply_symm tip_measurable]
  apply ne_top_of_le_ne_top width_integrable.lintegral_lt_top.ne
  apply lintegral_mono_ae
  have hv : ∀ᵐ v : Triple, v 0 ≠ 0 :=
    (quasiMeasurePreserving_eval (fun _ : Fin 3 => (volume : Measure ℝ)) 0).ae (volume.ae_ne 0)
  filter_upwards [quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) |>.ae hv] with w hw
  have he : (fun D : ℝ => (D,w)) ⁻¹' tip = Ioc 0 (width w) := by
    ext D
    simp [tip, hw]
  rw [he,Real.volume_Ioc,sub_zero]

private theorem width_single (u z D : ℝ) (hu : 0 < u) (hz : 0 < z)
    (H : (z*u)^2*D^3 ≤ 1024) :
    D ≤ 16 * u^(-(2/3):ℝ) * z^(-(2/3):ℝ) := by
  have cube (s : ℝ) (hs : 0 < s) : (s^(-(2/3):ℝ))^3 = (s^2)⁻¹ := by
    rw [← Real.rpow_mul_natCast hs.le]; norm_num
  have hn := Real.rpow_pos_of_pos hz (-(2/3):ℝ)
  have hn' := Real.rpow_pos_of_pos hu (-(2/3):ℝ)
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
  rw [mul_pow,mul_pow,cube u hu,cube z hz]
  field_simp
  nlinarith only [H]

theorem mem_tip {p D z S B : ℝ} (hD : 0 < D) (hp : 0 < p) (hp' : p < 1)
    (hz : |z| < 1) (hS : |S| ≤ 44) (hB : |B| ≤ 44)
    (H : (z*p*(1-p))^2*D^3 ≤ 256) : (D,p,![z,S,B]) ∈ tip := by
  refine ⟨hD,?_⟩
  by_cases h0 : z = 0
  · exact Or.inl h0
  right
  have hq : 0 < 1-p := sub_pos.mpr hp'
  have hz' : 0 < |z| := abs_pos.mpr h0
  have hZ : edge z + edge (-z) = |z|^(-(2/3):ℝ) := by
    rcases lt_or_gt_of_ne h0 with h|h
    · rw [abs_of_neg h] at *
      simp [edge,indicator_of_mem (show -z ∈ Ioo (0:ℝ) 1 from ⟨by linarith,hz⟩),
        indicator_of_notMem (show z ∉ Ioo (0:ℝ) 1 from fun H => h.not_gt H.1)]
    · rw [abs_of_pos h] at *
      simp [edge,indicator_of_mem (show z ∈ Ioo (0:ℝ) 1 from ⟨h,hz⟩),
        indicator_of_notMem (show -z ∉ Ioo (0:ℝ) 1 from fun H => (neg_neg_of_pos h).not_gt H.1)]
  have hS' := abs_le.mp hS
  have hB' := abs_le.mp hB
  change D ≤ width (p,![z,S,B])
  simp [width,Fin.prod_univ_three,weights,cutoff,hZ,show S ∈ Icc (-44:ℝ) 44 from hS',
    show B ∈ Icc (-44:ℝ) 44 from hB']
  unfold angular edge
  rw [indicator_of_mem (show p ∈ Ioo (0:ℝ) 1 from ⟨hp,hp'⟩),
    indicator_of_mem (show 1-p ∈ Ioo (0:ℝ) 1 from ⟨hq,by linarith⟩)]
  have HH : (|z| *p*(1-p))^2*D^3 ≤ 256 := by simpa only [mul_pow,sq_abs] using H
  have uni (u v : ℝ) (hu : 0 < u) (hv : 1/2 ≤ v)
      (h : (|z| *u*v)^2*D^3 ≤ 256) : D ≤ 16*u^(-(2/3):ℝ)*|z|^(-(2/3):ℝ) := by
    apply width_single _ _ _ hu hz'
    have hh : (1/2:ℝ)^2 ≤ v^2 := by nlinarith only [hv,sq_nonneg (v-1/2)]
    nlinarith only [h,mul_le_mul_of_nonneg_left hh (show 0 ≤ (|z| *u)^2*D^3 by positivity)]
  rcases le_total p (1/2) with h|h
  · have h' := uni p (1-p) hp (by linarith) HH
    nlinarith only [h', mul_nonneg (Real.rpow_nonneg hq.le (-(2/3):ℝ)) (Real.rpow_nonneg hz'.le (-(2/3):ℝ))]
  · have h' := uni (1-p) p hq h (by convert HH using 1; ring)
    nlinarith only [h', mul_nonneg (Real.rpow_nonneg hp.le (-(2/3):ℝ)) (Real.rpow_nonneg hz'.le (-(2/3):ℝ))]

end O71
