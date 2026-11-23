import Likelihood

noncomputable section
open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal
namespace O71
theorem likelihood_pos {n : ℕ} (f : ℝ → ℝ) (s : Sample n) : 0 < likelihood f s := by
  unfold likelihood ratio eexp
  exact CanonicallyOrderedAdd.prod_pos.mpr (fun i _ => ENNReal.ofReal_pos.mpr (exp_pos _))

theorem evidence_pos {n : ℕ} (s : Sample n) : 0 < evidence s := by
  have hm : Measurable (fun w => likelihood (prediction w) s) := by
    unfold likelihood ratio eexp prediction; fun_prop
  rw [evidence,lintegral_pos_iff_support hm]
  have h : Function.support (fun w => likelihood (prediction w) s) = univ :=
    eq_univ_of_forall (fun w => (likelihood_pos ..).ne')
  simp [h]

theorem evidence_finite {n : ℕ} (s : Sample n) : evidence s ≠ ∞ := by
  let upper := ∏ i, eexp (((s i).2)^2/2)
  have h (w : Space) : likelihood (prediction w) s ≤ upper := by
    apply Finset.prod_le_prod' 
    intro i _
    apply ENNReal.ofReal_le_ofReal
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg (prediction w (s i).1-(s i).2)]
  have hu := lintegral_mono (μ := prior) h
  simp only [lintegral_const,measure_univ,mul_one] at hu
  exact ne_top_of_le_ne_top (ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)) hu

theorem gaussian_factor (a y : ℝ) :
    gaussianPDFReal a 1 y = gaussianPDFReal 0 1 y * exp (a*y-a^2/2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,mul_assoc,←exp_add]
  congr 2
  ring

def trueDensity {n : ℕ} (s : Sample n) := ∏ i, gaussianPDFReal 0 1 (s i).2
def freeEnergy {n : ℕ} (s : Sample n) := -log (∫⁻ w, ∏ i, gaussianPDF (prediction w (s i).1) 1 (s i).2 ∂prior).toReal
def empiricalEntropy {n : ℕ} (s : Sample n) := -(∑ i, log (gaussianPDFReal 0 1 (s i).2))/(n:ℝ)

theorem freeEnergy_excess {n : ℕ} (hn : n ≠ 0) (s : Sample n) :
    freeEnergy s - n*empiricalEntropy s = excess s := by
  have hpos (i : Fin n) := gaussianPDFReal_pos 0 1 (s i).2 (by norm_num)
  have hprod : 0 < trueDensity s := Finset.prod_pos fun i _ => hpos i
  have h (w : Space) : (∏ i, gaussianPDF (prediction w (s i).1) 1 (s i).2) =
      ENNReal.ofReal (trueDensity s) * likelihood (prediction w) s := by
    simp only [gaussianPDF,gaussian_factor (prediction w _),ENNReal.ofReal_mul (hpos _).le,
      trueDensity,likelihood,eexp,ratio,Finset.prod_mul_distrib,ENNReal.ofReal_prod_of_nonneg (fun i _ => (hpos i).le)]
  unfold freeEnergy
  simp_rw [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hprod.le]
  change -log (trueDensity s*(evidence s).toReal) - _ = _
  rw [Real.log_mul hprod.ne' (ENNReal.toReal_pos (evidence_pos s).ne' (evidence_finite s)).ne']
  unfold trueDensity empiricalEntropy excess
  rw [Real.log_prod (fun i _ => (hpos i).ne')]
  field_simp
  ring
end O71
